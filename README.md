# lives-rs

Lifetime dynamic smart pointers.

[![CI Status][ci-badge]][ci-url]
[![MIT licensed][mit-badge]][mit-url]

[ci-badge]: https://github.com/aegistudio/lives-rs/actions/workflows/rust.yml/badge.svg
[ci-url]: https://github.com/aegistudio/lives-rs/actions/workflows/rust.yml
[mit-badge]: https://img.shields.io/badge/license-MIT-blue.svg
[mit-url]: https://github.com/aegistudio/lives-rs/blob/master/LICENSE

## Introduction

This crate aims at making weak pointers that may forget **covariant** lifetimes of a type. It relies on the fact that object may not outlive its covariant lifetime, and performs runtime checking of the liveness of the pointee object to determine the liveness of the forgotten lifetime. When it's alive, the weak pointer allows the caller to perform actions on a reference to the pointee object borrowed for a lifetime strictly contained in the covariant lifetime of the object, while forbidding the caller from extending it.

This allows us to write:

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

The standard library `Weak` pointer will not allow you to do that, since it's otherwise prone to upgrading the weak pointer to an `Rc` and holding it, extending lifetime for arbitrarily long. Our crate think differently by forbidding the upgrade of a `LifeWeak` pointer back to `LifeRc` pointer, and regulating the access of reference to the still alive pointee, by constraining the borrow lifetime.

The introduction above explains the idea but might be oversimplifying the constraints of this crate. For more detail, please see the [documentation](https://docs.rs/lives).

# License

This project is licensed under the [MIT license].

[MIT license]: https://github.com/aegistudio/lives-rs/blob/master/LICENSE