//! Lifetime-dynamic smart pointers.
//!
//! In short, this crate is useful when you want
//! to deal with objects annotated with lifetime.
//! More specifically, when you create weak
//! pointers [`LifeWeak`] to these objects, so that:
//!
//! - The pointee objects live in their own
//!   lifetimes, respecting the borrow checker.
//! - With the weak pointer, the caller may
//!   operate on pointee objects that are
//!   still alive, and ignore those who have
//!   gone out of their own lifetimes.
//! - The lifetime parameters of pointee type
//!   are masked on the weak pointer
//!   (e.g. `Obj<'a> -> LifeWeak<Obj<'static>>`)
//!   to annotate lifetime checking as dynamic,
//!   so that the weak pointers can be held as
//!   fields or stored in containers.
//!
//! This crate works under these
//! <b id="premises">premises</b>:
//!
//! 1. If a lifetime `'a` is alive before
//! calling a function, then it will at least be
//! alive until returning from this function.
//! 2. The pointee `Obj<'a>` is (reducible
//! to be) parameterized by a single lifetime
//! parameter `'a` and
//! [**covariant**](https://doc.rust-lang.org/reference/subtyping.html#variance)
//! over lifetime `'a`.
//! That is, if `'b` is a lifetime completely
//! contained in `'a`, then `Obj<'a>` can
//! be used in place of `Obj<'b>`.
//! 3. When operating on the pointee object
//! from [`LifeWeak<Obj<'static>>`], either
//! no [`LifeRc<Obj<'a>>`] is dropped, or
//! the [`Drop::drop`] behavior of `Obj<'a>`
//! is **completely irrelevant** to its
//! lifetime parameter `'a`.
//!
//! These premises can be held at most of
//! cases. But if any of these premises is
//! broken, then the behavior of this crate
//! is undefined.
//!
//! # Why [`Rc`] and [`Weak`] don't suffice?
//!
//! To illustrate the problem, imagine a
//! <text id="previous-example">scenario</text>
//! where lifetime annotated object
//! **must** be used:
//!
#![doc = r##"
```rust,compile_fail
use std::rc::{Rc, Weak};

// While it's possible to hold a String here
// to get rid of the lifetime problem, we are
// just writing so to simulate an object
// annotated with lifetime.
struct Str<'a> (&'a str);

fn main() {
    let mut weaks: Vec<Weak<Str<'_>>> = Vec::new();
    
    {
        let a = format!("{}", 123456);
        let a_rc = Rc::new(Str(a.as_str()));
        weaks.push(Rc::downgrade(&a_rc));
        // Dropping `a` here is intended, to
        // simulate the case when the pointee
        // of weak pointer goes out of lifetime.
    }
    
    let b = format!("{}", 789012);
    let b_rc = Rc::new(Str(b.as_str()));
    weaks.push(Rc::downgrade(&b_rc));
    
    for weak in weaks {
        if let Some(rc) = weak.upgrade() {
            println!("{}", rc.0);
        }
    }
}
```
"##]
//!
//! Let's assume the attention of writing
//! so is: While some of these `Str<'_>`
//! object may go out of scope, we just
//! care about the ones that are still
//! alive, and print them out.
//!
//! When you plug the code into rust compiler,
//! the borrow checker will soon complain
//! about that `a.as_str()` borrows `a`
//! while it does not live long enough.
//! However, the intention of this code
//! is to allow `a` to drop, in that case,
//! the weak pointer `Rc::downgrade(&a_rc)`
//! should dereference to `None`.
//!
//! While the error originates from the
//! borrow checker, I would say it's rather
//! a type error. We know lifetimes are built
//! into rust types, and in the code above,
//! the borrow checker will attempt to infer
//! the ellided lifetime of `Vec<Weak<Str<'_>>>`.
//! However, it's **impossible** to infer
//! such a correct lifetime, since it will
//! be otherwise self-contradictory:
//!
//! - If the lifetime is as long as the block
//!   where `a` is in, let it be `'a`, then
//!   `weaks: Vec<Weak<Str<'a>>>` continues
//!   to live after exiting the block `a` is
//!   in, which violates the rule of an object
//!   cannot outlives its lifetime annotation.
//! - If the lifetime is as long as the one
//!   where `weaks` and `b` is in, let it be
//!   `'b`, then `Rc::downgrade(&a_rc)` is not
//!   assignable to `Weak<Str<'b>>`, as it does
//!   not live long enough to be `'b`.
//!
//! In fact, although we won't be able to
//! access a dead `Str<'_>` with `Weak<Str<'_>>`,
//! there's no way to "slack" the lifetime on
//! `Weak<Str<'_>>`, since the standard library
//! has a good reason to adhere the lifetime:
//! Let there be a weak pointer
//! `weak: Weak<Str<'c>>` from `rc: Rc<Str<'c>>`,
//! if we upgrade it back to `Some(Rc<Str<'c>>)`
//! by `weak.upgrade()` successfully, then
//! such an upgraded pointer truly holds an
//! object of `Str<'c>`, which must not outlive
//! `'c`. Therefore, as long as we are able to
//! recover a `Weak<Str<'_>>` back to a
//! `Rc<Str<'_>>`, the lifetime is mandatory.
//!
//! # Our method
//!
//! Generally speaking, we diverge from the
//! standard library by forbidding the upgrade
//! of a weak pointer [`LifeWeak`]. Instead,
//! the caller pass a callback function to
//! [`LifeWeak::with`], then the weak pointer
//! checks if the pointee is still alive,
//! "fix" the lifetime of the reference to
//! the pointee, to a reasonably short one,
//! and finally pass the reference into
//! the callback to perform the operation.
//!
//! Let the pointee type be `t: Obj<'a>`,
//! and we use **pseudo** rust code to
//! illustrate the idea.
//!
//! First, the user create
//! reference counting [`LifeRc<Obj<'a>>`]
//! out of `t`. The reference-counting
//! pointer is annotated with the lifetime
//! `'a` and respect the borrow checker:
//!
#![doc = r##"
```rust,compile_fail
use std::rc::Rc;
struct LifeRc<T> {
    internal: Rc<T>,
}

fn new<'a>(t: Obj<'a>) -> LifeRc<Obj<'a>> {
    LifeRc { internal: Rc::new(t) }
}
```
"##]
//!
//! Then, the user downgrade [`LifeRc<Obj<'a>>`]
//! to weak pointer [`LifeWeak<Obj<'static>>`],
//! and send it to the weak consumer of `t`.
//! The lifetime `'static` means we want
//! to detach the lifetime from `'a` and
//! check it at runtime:
//!
#![doc = r##"
```rust,compile_fail
use std::rc::Weak;
struct LifeWeak<T> {
    internal: Weak<T>,
}

fn downgrade<'a>(rc: &LifeRc<Obj<'a>>) -> LifeWeak<Obj<'static>> {
    let weak: Weak<Obj<'a>> = Rc::downgrade(&rc.internal);
    let internal: Weak<Obj<'static>> = edit_lifetime::<'static>(weak);
    LifeWeak { internal }
}
```
"##]
//!
//! Finally, the weak consumer of `t` pass a
//! callback to [`LifeWeak<Obj<'static>>::with`],
//! to perform acton on `t`:
//!
#![doc = r##"
```rust,compile_fail
fn with<F, U>(
    weak: &LifeWeak<Obj<'static>>, callback: F,
) -> Option<U>
where
    F: for<'b> FnOnce(&'b Obj<'b>) -> U,
{
    'b: {
        let rc: Rc<Obj<'static>> = weak.internal.upgrade()?;
        let t: &'b Obj<'b> = edit_lifetime::<'b>(&*rc);
        Some(callback(t))
    } // end of 'b
}
```
"##]
//!
//! Let's give a closer look at why
//! [`LifeWeak<Obj<'static>>::with`] works.
//! Recall that we made some [premises](#premises),
//! they are applicable now:
//!
//! 1. In the [`LifeWeak<Obj<'static>>::with`]
//! function, if we are able to upgrade the
//! internal weak pointer, then at least one
//! reference counting [`Rc<Obj<'a>>`] is still
//! alive, since a [`Rc<Obj<'a>>`] cannot outlives
//! `'a`, lifetime `'a` must have been alive
//! before entering [`LifeWeak<Obj<'static>>::with`],
//! By **premise #1**,  `'a` is alive during the
//! **whole** execution of the
//! [`LifeWeak<Obj<'static>>::with`] function.
//!
//! 2. Therefore lifetime `'b` is completely
//! contained in `'a`. In the function
//! [`LifeWeak<Obj<'static>>::with`], we
//! reconstruct the lifetime of `Obj<'a>`
//! into `Obj<'b>`, and by **premise #2**
//! that `Obj<'a>` is covariant, plus the
//! variance rule of an immutable pointer,
//! we can use `&*rc: &'b Obj<'a>`
//! in the place of `&'b Obj<'b>`.
//! Thus `t` is well-formed.
//!
//! 3. By **premise #3**, either we
//! won't drop any [`LifeRc<Obj<'a>>`] during
//! the execution of `callback`, so that we
//! don't ever need to care about calling
//! `Obj<'static>::drop`; or the [`Drop::drop`]
//! of `Obj<'a>` is irrelevant to its lifetime
//! `'a`, and thus calling `Obj<'static>::drop`
//! and `Obj<'a>::drop` are equivalent.In
//! either way,  `Rc<Obj<'a>>` will be
//! maintained correctly.
//!
//! With our method, we can fix the
//! [previous example](#previous-example) into:
#![doc = r##"
```rust
use lives::{Life, LifeRc, LifeWeak};

#[derive(Life)]
struct Str<'a> (&'a str);

fn main() {
    let mut weaks: Vec<LifeWeak<Str<'static>>> = Vec::new();
    
    {
        let a = format!("{}", 123456);
        let a_rc = LifeRc::new(Str(a.as_str()));
        weaks.push(LifeRc::downgrade(&a_rc));
    }
    
    let b = format!("{}", 789012);
    let b_rc = LifeRc::new(Str(b.as_str()));
    weaks.push(LifeRc::downgrade(&b_rc));
    
    for weak in weaks {
        weak.with(|r| println!("{}", r.0));
    }
}
```
"##]

use std::ops::Deref;
use std::rc::{Rc, Weak};

/// Lifetime-bounded type trait.
///
/// To wrap object into [`LifeRc`] and [`LifeWeak`],
/// you must first teach them how to transform the
/// lifetimes. To do so, you define the associate
/// type [`Life::Timed`], which has a lifetime
/// parameter, then [`LifeRc`] and [`LifeWeak`]
/// can plug the correct lifetime into it.
///
/// The user must also prove the covariance of
/// the object, by implementing the covariance
/// method. Normally it can be done by simply
/// returning the input object.
pub trait Life {
    type Timed<'b>: 'b + Life;

    /// Prove the covariance.
    ///
    /// For a lifetime `'c` which is completely
    /// contained in `'b`, show that `Obj<'b>`
    /// can be used in the place of `Obj<'c>`.
    /// This should be normally be done by
    /// returing the input.
    ///
    /// This function will never be called, it's
    /// just pressing the user to check it.
    /// Of course, the user can just put a
    /// `todo!()` into it and take their own
    /// risk, there's nothing stopping them.
    fn covariance<'c, 'b: 'c>(a: Self::Timed<'b>) -> Self::Timed<'c>;
}

impl<'a, T: Life + ?Sized> Life for &'a T {
    type Timed<'b> = &'b T::Timed<'b>;

    fn covariance<'c, 'b: 'c>(a: &'b T::Timed<'b>) -> &'c T::Timed<'c> {
        // First, T::Timed<'b> is covariant over
        // 'b, for 'c completely contained in 'b,
        // T::Timed<'b> can be used in the place
        // of T::Timed<'c>. Now we've got a
        // reference &'b T::Timed<'c>.
        // Then the reference itself can be
        // casted into &'c T::Timed<'c>.
        unsafe { std::mem::transmute(a) }
    }
}

impl<'a, T: 'static + ?Sized> Life for &'a mut T {
    type Timed<'b> = &'b mut T;

    fn covariance<'c, 'b: 'c>(a: &'b mut T) -> &'c mut T {
        a
    }
}

impl<T: Life> Life for Option<T> {
    type Timed<'b> = Option<T::Timed<'b>>;

    fn covariance<'c, 'b: 'c>(a: Self::Timed<'b>) -> Self::Timed<'c> {
        Some(T::covariance(a?))
    }
}

impl<T: Life> Life for Box<T> {
    type Timed<'b> = Box<T::Timed<'b>>;

    fn covariance<'c, 'b: 'c>(a: Self::Timed<'b>) -> Self::Timed<'c> {
        Box::new(T::covariance(*a))
    }
}

impl<T: Life> Life for Vec<T> {
    type Timed<'b> = Vec<T::Timed<'b>>;

    fn covariance<'c, 'b: 'c>(a: Self::Timed<'b>) -> Self::Timed<'c> {
        let mut result = Vec::new();
        for item in a {
            result.push(T::covariance(item));
        }
        result
    }
}

macro_rules! impl_life_for_primitive {
    ($ty: ty) => {
        impl Life for $ty {
            type Timed<'b> = $ty;

            fn covariance<'c, 'b: 'c>(a: $ty) -> $ty {
                a
            }
        }
    };
}

impl_life_for_primitive!(());
impl_life_for_primitive!(bool);
impl_life_for_primitive!(char);

impl<'a> Life for &'a str {
    type Timed<'b> = &'b str;

    fn covariance<'c, 'b: 'c>(a: Self::Timed<'b>) -> Self::Timed<'c> {
        a
    }
}

impl_life_for_primitive!(u8);
impl_life_for_primitive!(u16);
impl_life_for_primitive!(u32);
impl_life_for_primitive!(u64);
impl_life_for_primitive!(u128);
impl_life_for_primitive!(usize);

impl_life_for_primitive!(i8);
impl_life_for_primitive!(i16);
impl_life_for_primitive!(i32);
impl_life_for_primitive!(i64);
impl_life_for_primitive!(i128);
impl_life_for_primitive!(isize);

impl_life_for_primitive!(f32);
impl_life_for_primitive!(f64);

/// Lifetime-bounding reference-counting pointer.
///
/// This reference pointer is just like
/// [`std::rc::Rc`]. The pointee `t: Obj<'a>`,
/// will be wrapped into `LifeRc<Obj<'a>>`,
/// therefore any `LifeRc<'a>` of `t` will
/// not be able to outlives lifetime `'a`.
/// The purpose of this pointer type is to
/// control the weak pointers [`LifeWeak`].
/// We forbid upgrading [`LifeWeak`] back to
/// [`LifeRc`], and allow only using
/// [`LifeWeak::with`] to access the currently
/// available reference to `t`. If all
/// [`LifeRc`] created for `t` has gone
/// out of scope, then none of these
/// [`LifeWeak::with`] will be able
/// to acquire a reference to  `t`.
///
/// This pointer works only under
/// single-threaded context, and is immutable
/// after creation as it can be shared (this
/// is the same as [`std::rc::Rc`]). You
/// must cope with [`std::cell::RefCell`]
/// and interior mutability if you want
/// to mutate the pointee.
///
/// Check the premises of in the [module
/// level documentation](crate) to see
/// the constraints about this pointer.
#[derive(Clone)]
pub struct LifeRc<T: Life> {
    internal: Rc<T>,
}

impl<T: Life> LifeRc<T> {
    pub fn new(t: T) -> Self {
        Self {
            internal: Rc::new(t),
        }
    }
}

impl<T: Life> Deref for LifeRc<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &*self.internal
    }
}

/// Lifetime-dynamic weak pointer.
///
/// This pointer is just like
/// [`std::rc::Weak`], it's the weak
/// pointer of [`LifeRc`] to some
/// pointee `t: Obj<'a>`. However, unlike
/// the standard library one, we are
/// **forbidden** from upgrading this weak
/// pointer back to [`LifeRc`] again, since
/// doing so opens the door to accidentally
/// and arbitrarily prolonging the lifetime
/// `'a` (by holding the upgraded
/// [`LifeRc`] for arbitrarily long).
/// Instead, we allow accessing `t` only
/// by [`LifeWeak::with`], where we check
/// if there's any alive [`LifeRc`] to `t`
/// before performing any action on `t`.
/// Since any [`LifeRc`] to `t` cannot
/// outlives `'a`, if we acquire `t`
/// successfully, it's still under `'a`.
/// And assume it's a single-threaded
/// context, so after checking the liveness
/// of `t`, we perform the operation on
/// `t`, which is mutually exclusive with the
/// descruction of any [`LifeRc`] of `t`
/// (unless you deliberately drop the last
/// [`LifeRc`] in the middle of the operation,
/// which will be checked separately).
///
/// Therefore, a reference-counting
/// pointer `LifeRc<Obj<'a>>` is
/// downgraded to `LifeWeak<Obj<'static>>`,
/// where `'static` means the pointee is
/// available when we've checked it
/// to be available.
///
/// Check the premises of in the [module
/// level documentation](crate) to see
/// the constraints about this pointer.
pub struct LifeWeak<T: Life> {
    internal: Weak<T::Timed<'static>>,
}

impl<T: Life> LifeWeak<T> {
    fn within<'a, F, U>(rc: &'a Rc<T::Timed<'static>>, f: F) -> U
    where
        F: for<'b> FnOnce(&'b T::Timed<'b>) -> U,
    {
        let t: &'a T::Timed<'a> = unsafe { std::mem::transmute(rc.as_ref()) };
        f(t)
    }

    /// Perform operation on currently alive pointee.
    ///
    /// Since the lifetime of `T` has been masked
    /// with `'static` and is unrecoverable, to
    /// prevent the operation from accidentally
    /// prolonging the lifetime, we pass an
    /// **arbitrary short** lifetime reference
    /// `for<'b> &'b T` to the operation.
    ///
    /// For example, if you write `|t| &t.some_field`,
    /// to return a reference to a field of `t`,
    /// then the borrow checker will start to
    /// complain since the lifetime `'b` of `t`
    /// can be arbitrary short and `&'b t.some_field`
    /// may not live long enough.
    pub fn with<F, U>(&self, f: F) -> Option<U>
    where
        F: for<'b> FnOnce(&'b T::Timed<'b>) -> U,
    {
        let rc = self.internal.upgrade()?;
        Some(Self::within(&rc, f))
    }
}

impl<T: Life> LifeRc<T> {
    /// Downgrade the reference-counting pointer
    /// to a weak pointer.
    pub fn downgrade(rc: &LifeRc<T>) -> LifeWeak<T::Timed<'static>> {
        let weak = Rc::downgrade(&rc.internal);
        LifeWeak {
            internal: unsafe { std::mem::transmute(weak) },
        }
    }
}

/// Simply implement [`Life`] for the specific type.
///
/// This derive macro will simply meld all lifetime parameters
/// into one so that it fulfills the requirement of a pointee
/// type due to the [`crate`].
///
/// The generated covariance method will assert the type is
/// covariant and simply implementing [`Life::covariance`]
/// as returning the input. If it fails to compile, it's a
/// good signal that your type is not covariant, and you
/// should consider picking the invariant and contravariant
/// ones out and put in into the generic parameters yourself.
///
/// In short, if this derive macro does not work for you,
/// you must consider implementing [`Life`] yourself.
pub use lives_macros::Life;

#[cfg(test)]
mod test {
    use crate::{Life, LifeRc, LifeWeak};

    #[test]
    fn test_objects() {
        #[derive(Life)]
        struct StrHolder<'a> {
            s: &'a str,
        }

        let mut weaks: Vec<LifeWeak<StrHolder<'static>>> = Vec::new();

        {
            let a = "a".to_string();
            let a_rc = LifeRc::new(StrHolder { s: a.as_str() });
            weaks.push(LifeRc::downgrade(&a_rc));
        }
        let b = "b".to_string();
        let b_rc = LifeRc::new(StrHolder { s: b.as_str() });
        weaks.push(LifeRc::downgrade(&b_rc));

        let mut result: Vec<String> = Vec::new();
        for weak in weaks {
            if let Some(s) = weak.with(|r| r.s.to_string()) {
                result.push(s);
            }
        }
        assert_eq!(result, ["b"]);
    }

    #[test]
    fn test_references_1() {
        let mut weaks: Vec<LifeWeak<&'static str>> = Vec::new();

        {
            let a = "a".to_string();
            let a_rc = LifeRc::new(a.as_str());
            weaks.push(LifeRc::downgrade(&a_rc));
        }
        let b = "b".to_string();
        let b_rc = LifeRc::new(b.as_str());
        weaks.push(LifeRc::downgrade(&b_rc));

        let mut result: Vec<String> = Vec::new();
        for weak in weaks {
            if let Some(s) = weak.with(|r| r.to_string()) {
                result.push(s);
            }
        }
        assert_eq!(result, ["b"]);
    }

    #[test]
    fn test_references_2() {
        let mut weaks: Vec<LifeWeak<&'static u64>> = Vec::new();

        {
            let a = 12345u64;
            let a_rc = LifeRc::new(&a);
            weaks.push(LifeRc::downgrade(&a_rc));
        }
        let b = 45678u64;
        let b_rc = LifeRc::new(&b);
        weaks.push(LifeRc::downgrade(&b_rc));
        {
            let c = 78901u64;
            let c_rc = LifeRc::new(&c);
            weaks.push(LifeRc::downgrade(&c_rc));
        }

        let mut accum = 0;
        for weak in weaks {
            accum += weak.with(|v| **v).unwrap_or(0);
        }
        assert_eq!(accum, 45678);
    }

    #[test]
    fn test_option_references() {
        let mut weaks: Vec<LifeWeak<Option<&'static str>>> = Vec::new();

        {
            let a = "a".to_string();
            let a_rc = LifeRc::new(Some(a.as_str()));
            weaks.push(LifeRc::downgrade(&a_rc).into());
        }
        let b = "b".to_string();
        let b_rc = LifeRc::new(Some(b.as_str()));
        weaks.push(LifeRc::downgrade(&b_rc).into());

        let mut result: Vec<String> = Vec::new();
        for weak in weaks {
            if let Some(s) = weak.with(|r| r.unwrap().to_string()) {
                result.push(s);
            }
        }
        assert_eq!(result, ["b"]);
    }

    #[test]
    fn test_dyn_boxes() {
        #[derive(Default)]
        struct Context {
            a: usize,
            b: Vec<String>,
        }

        trait Trait {
            fn action(&self, cx: &mut Context);
        }

        #[derive(Life)]
        struct BoxDynTrait<'a>(Box<dyn Trait + 'a>);

        struct TraitImplStr<'a> {
            s: &'a str,
        }

        impl<'a> Trait for TraitImplStr<'a> {
            fn action(&self, cx: &mut Context) {
                cx.a += self.s.len();
                cx.b.push(self.s.to_string());
            }
        }

        struct TraitImplClear;

        impl Trait for TraitImplClear {
            fn action(&self, cx: &mut Context) {
                cx.a = 0;
                cx.b.clear();
            }
        }

        let mut weaks: Vec<LifeWeak<BoxDynTrait<'static>>> = Vec::new();

        {
            let a = "a".to_string();
            let a_bx = BoxDynTrait(Box::new(TraitImplStr { s: a.as_str() }));
            let a_rc = LifeRc::new(a_bx);
            weaks.push(LifeRc::downgrade(&a_rc).into());
        }
        let bcd = "bcd".to_string();
        let bcd_bx = BoxDynTrait(Box::new(TraitImplStr { s: bcd.as_str() }));
        let bcd_rc = LifeRc::new(bcd_bx);
        weaks.push(LifeRc::downgrade(&bcd_rc).into());
        {
            let clr_bx = BoxDynTrait(Box::new(TraitImplClear));
            let clr_rc = LifeRc::new(clr_bx);
            weaks.push(LifeRc::downgrade(&clr_rc).into());
        }

        let mut cx = Context::default();
        for weak in weaks {
            weak.with(|o| o.0.action(&mut cx));
        }
        assert_eq!(cx.a, 3);
        assert_eq!(cx.b, ["bcd"]);
    }
}
