# `applin_headless`

[![crates.io version](https://img.shields.io/crates/v/applin_headless.svg)](https://crates.io/crates/applin_headless)
[![unsafe forbidden](https://raw.githubusercontent.com/leonhard-llc/applin-headless-rust/main/unsafe-forbidden-success.svg)](https://github.com/rust-secure-code/safety-dance/)
[![pipeline status](https://github.com/leonhard-llc/applin-headless-rust/workflows/CI/badge.svg)](https://github.com/leonhard-llc/applin-headless-rust/actions)

Create an Applin™ client and control it from Rust code. Great for tests.

<https://www.applin.dev/>

# Cargo Geiger Safety Report
```

Metric output format: x/y
    x = unsafe code used by the build
    y = total unsafe code found in the crate

Symbols: 
    🔒  = No `unsafe` usage found, declares #![forbid(unsafe_code)]
    ❓  = No `unsafe` usage found, missing #![forbid(unsafe_code)]
    ☢️  = `unsafe` usage found

Functions  Expressions  Impls  Traits  Methods  Dependency

0/0        0/0          0/0    0/0     0/0      🔒  applin_headless 0.2.0
0/0        0/0          0/0    0/0     0/0      🔒  ├── applin 0.2.9
0/0        7/20         0/0    0/0     0/0      ☢️  │   ├── nanorand 0.7.0
0/0        5/5          0/0    0/0     0/0      ☢️  │   ├── serde 1.0.197
0/0        0/0          0/0    0/0     0/0      ❓  │   │   └── serde_derive 1.0.197
0/0        15/15        0/0    0/0     3/3      ☢️  │   │       ├── proc-macro2 1.0.79
0/0        4/4          0/0    0/0     0/0      ☢️  │   │       │   └── unicode-ident 1.0.12
0/0        0/0          0/0    0/0     0/0      ❓  │   │       ├── quote 1.0.35
0/0        15/15        0/0    0/0     3/3      ☢️  │   │       │   └── proc-macro2 1.0.79
0/0        80/80        3/3    0/0     2/2      ☢️  │   │       └── syn 2.0.53
0/0        15/15        0/0    0/0     3/3      ☢️  │   │           ├── proc-macro2 1.0.79
0/0        0/0          0/0    0/0     0/0      ❓  │   │           ├── quote 1.0.35
0/0        4/4          0/0    0/0     0/0      ☢️  │   │           └── unicode-ident 1.0.12
0/0        4/7          0/0    0/0     0/0      ☢️  │   └── serde_json 1.0.114
0/0        76/81        1/1    0/0     0/0      ☢️  │       ├── indexmap 2.2.5
0/0        0/0          0/0    0/0     0/0      ❓  │       │   ├── equivalent 1.0.1
1/1        1411/1586    21/24  1/1     76/88    ☢️  │       │   ├── hashbrown 0.14.3
0/0        0/0          0/0    0/0     0/0      ❓  │       │   │   ├── equivalent 1.0.1
0/0        5/5          0/0    0/0     0/0      ☢️  │       │   │   └── serde 1.0.197
0/0        5/5          0/0    0/0     0/0      ☢️  │       │   └── serde 1.0.197
0/0        7/7          0/0    0/0     0/0      ☢️  │       ├── itoa 1.0.10
7/9        572/702      0/0    0/0     2/2      ☢️  │       ├── ryu 1.0.17
0/0        5/5          0/0    0/0     0/0      ☢️  │       └── serde 1.0.197
0/0        0/0          0/0    0/0     0/0      ❓  ├── cookie_store 0.21.0
0/0        0/0          0/0    0/0     0/0      ❓  │   ├── cookie 0.18.0
0/0        0/0          0/0    0/0     0/0      🔒  │   │   ├── base64 0.21.7
0/0        8/8          0/0    0/0     0/0      ☢️  │   │   ├── percent-encoding 2.3.1
1/2        219/246      0/0    0/0     4/4      ☢️  │   │   └── time 0.3.36
1/1        4/4          0/0    0/0     1/1      ☢️  │   │       ├── deranged 0.3.11
2/2        29/29        0/0    0/0     0/0      ☢️  │   │       │   ├── powerfmt 0.2.0
0/0        5/5          0/0    0/0     0/0      ☢️  │   │       │   └── serde 1.0.197
0/0        7/7          0/0    0/0     0/0      ☢️  │   │       ├── itoa 1.0.10
0/0        0/0          0/0    0/0     0/0      ❓  │   │       ├── num-conv 0.1.0
2/2        29/29        0/0    0/0     0/0      ☢️  │   │       ├── powerfmt 0.2.0
0/0        5/5          0/0    0/0     0/0      ☢️  │   │       ├── serde 1.0.197
0/0        0/0          0/0    0/0     0/0      ❓  │   │       ├── time-core 0.1.2
0/0        0/0          0/0    0/0     0/0      ❓  │   │       └── time-macros 0.2.18
0/0        0/0          0/0    0/0     0/0      ❓  │   │           ├── num-conv 0.1.0
0/0        0/0          0/0    0/0     0/0      ❓  │   │           └── time-core 0.1.2
0/0        0/0          0/0    0/0     0/0      ❓  │   ├── idna 0.5.0
0/0        5/5          0/0    0/0     0/0      ☢️  │   │   ├── unicode-bidi 0.3.15
0/0        5/5          0/0    0/0     0/0      ☢️  │   │   │   └── serde 1.0.197
0/0        20/20        0/0    0/0     0/0      ☢️  │   │   └── unicode-normalization 0.1.23
0/0        0/0          0/0    0/0     0/0      🔒  │   │       └── tinyvec 1.6.0
0/0        5/5          0/0    0/0     0/0      ☢️  │   │           ├── serde 1.0.197
0/0        0/0          0/0    0/0     0/0      🔒  │   │           └── tinyvec_macros 0.1.1
0/0        76/81        1/1    0/0     0/0      ☢️  │   ├── indexmap 2.2.5
2/2        18/18        1/1    0/0     0/0      ☢️  │   ├── log 0.4.21
0/0        5/5          0/0    0/0     0/0      ☢️  │   │   └── serde 1.0.197
0/0        5/5          0/0    0/0     0/0      ☢️  │   ├── serde 1.0.197
0/0        0/0          0/0    0/0     0/0      ❓  │   ├── serde_derive 1.0.197
0/0        4/7          0/0    0/0     0/0      ☢️  │   ├── serde_json 1.0.114
1/2        219/246      0/0    0/0     4/4      ☢️  │   ├── time 0.3.36
0/0        0/0          0/0    0/0     0/0      ❓  │   └── url 2.5.0
0/0        2/2          0/0    0/0     0/0      ☢️  │       ├── form_urlencoded 1.2.1
0/0        8/8          0/0    0/0     0/0      ☢️  │       │   └── percent-encoding 2.3.1
0/0        0/0          0/0    0/0     0/0      ❓  │       ├── idna 0.5.0
0/0        8/8          0/0    0/0     0/0      ☢️  │       ├── percent-encoding 2.3.1
0/0        5/5          0/0    0/0     0/0      ☢️  │       └── serde 1.0.197
0/0        0/0          0/0    0/0     0/0      🔒  ├── ureq 2.9.6
0/0        0/0          0/0    0/0     0/0      🔒  │   ├── base64 0.21.7
0/0        0/0          0/0    0/0     0/0      ❓  │   ├── cookie 0.18.0
0/0        0/0          0/0    0/0     0/0      ❓  │   ├── cookie_store 0.21.0
2/2        18/18        1/1    0/0     0/0      ☢️  │   ├── log 0.4.21
0/0        74/117       5/9    0/0     2/4      ☢️  │   ├── once_cell 1.19.0
0/0        5/5          0/0    0/0     0/0      ☢️  │   ├── serde 1.0.197
0/0        4/7          0/0    0/0     0/0      ☢️  │   ├── serde_json 1.0.114
0/0        0/0          0/0    0/0     0/0      ❓  │   └── url 2.5.0
0/0        0/0          0/0    0/0     0/0      ❓  └── url 2.5.0

14/17      2560/2956    31/38  1/1     90/104 

```
# Changelog
- v0.2.0 2024-11-13
    - Add `cookie_file_path` arg to `ApplinClient::new`.
    - Add `log_pages`.
- v0.1.1 2024-11-03 - Add `is_checked`.
- v0.1.0 - Impersonates applin-ios 0.38.0.
