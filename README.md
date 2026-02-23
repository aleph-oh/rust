# The Rust Programming Language

[![Rust Community](https://img.shields.io/badge/Rust_Community%20-Join_us-brightgreen?style=plastic&logo=rust)](https://www.rust-lang.org/community)

This is the main source code repository for [Rust]. It contains the compiler,
standard library, and documentation.

[Rust]: https://www.rust-lang.org/

**Note: this README is for _users_ rather than _contributors_.**
If you wish to _contribute_ to the compiler, you should read
[CONTRIBUTING.md](CONTRIBUTING.md) instead.

<details>
<summary>Table of Contents</summary>

- [Quick Start](#quick-start)
- [Installing from Source](#installing-from-source)
- [Getting Help](#getting-help)
- [Contributing](#contributing)
- [License](#license)
- [Trademark](#trademark)

</details>

## Quick Start

Read ["Installation"] from [The Book].

["Installation"]: https://doc.rust-lang.org/book/ch01-01-installation.html
[The Book]: https://doc.rust-lang.org/book/index.html

## Installing from Source

If you really want to install from source (though this is not recommended), see
[INSTALL.md](INSTALL.md).

## Getting Help

See https://www.rust-lang.org/community for a list of chat platforms and forums.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

## Required Environment Variables
The compiler uses the environment variables *OPENCILK_ABI_PATH* and *OPENCILK_RT_SEARCH_DIR*. 
Although bootstrapping the compiler does not require setting either of these above environment variables, 
invoking its test suite with "./x test" will. After bootstrapping, running a command like find build -name "libopencilk*" 
should give both the directory containing the OpenCilk runtime shared library and the path to the bitcode file (a filename which ends in .bc). 
OPENCILK_ABI_PATH should be set to the path to the bitcode file, and 
OPENCILK_RT_SEARCH_DIR should be set to the directory containing the runtime's shared library. 
Exporting these variables in some file like .bashrc or .zshrc should make this requirement less tedious to accommodate 
until some changes to make rustc search for the OpenCilk runtime shared library and the correct bitcode file are done.

## License

Rust is primarily distributed under the terms of both the MIT license and the
Apache License (Version 2.0), with portions covered by various BSD-like
licenses.

See [LICENSE-APACHE](LICENSE-APACHE), [LICENSE-MIT](LICENSE-MIT), and
[COPYRIGHT](COPYRIGHT) for details.

## Trademark

[The Rust Foundation][rust-foundation] owns and protects the Rust and Cargo
trademarks and logos (the "Rust Trademarks").

If you want to use these names or brands, please read the
[media guide][media-guide].

Third-party logos may be subject to third-party copyrights and trademarks. See
[Licenses][policies-licenses] for details.

[rust-foundation]: https://foundation.rust-lang.org/
[media-guide]: https://foundation.rust-lang.org/policies/logo-policy-and-media-guide/
[policies-licenses]: https://www.rust-lang.org/policies/licenses
