# `applin_headless`

[![crates.io version](https://img.shields.io/crates/v/applin.svg)](https://crates.io/crates/applin_headless)
[![unsafe forbidden](https://raw.githubusercontent.com/leonhard-llc/applin-headless-rust/main/unsafe-forbidden-success.svg)](https://github.com/rust-secure-code/safety-dance/)
[![pipeline status](https://github.com/leonhard-llc/applin-headless-rust/workflows/CI/badge.svg)](https://github.com/leonhard-llc/applin-rust/actions)

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

0/0        0/0          0/0    0/0     0/0      🔒  applin_headless 0.1.0
0/0        0/0          0/0    0/0     0/0      🔒  ├── applin 0.2.7
0/0        7/20         0/0    0/0     0/0      ☢️  │   ├── nanorand 0.7.0
3/7        47/225       0/1    0/0     1/3      ☢️  │   │   ├── getrandom 0.2.12
0/0        0/0          0/0    0/0     0/0      ❓  │   │   │   ├── cfg-if 1.0.0
1/90       10/582       0/2    0/0     5/63     ☢️  │   │   │   └── libc 0.2.153
1/1        22/22        0/0    0/0     0/0      ☢️  │   │   └── zeroize 1.7.0
0/0        5/5          0/0    0/0     0/0      ☢️  │   │       └── serde 1.0.197
0/0        0/0          0/0    0/0     0/0      ❓  │   │           └── serde_derive 1.0.197
0/0        15/15        0/0    0/0     3/3      ☢️  │   │               ├── proc-macro2 1.0.79
0/0        4/4          0/0    0/0     0/0      ☢️  │   │               │   └── unicode-ident 1.0.12
0/0        0/0          0/0    0/0     0/0      ❓  │   │               ├── quote 1.0.35
0/0        15/15        0/0    0/0     3/3      ☢️  │   │               │   └── proc-macro2 1.0.79
0/0        80/80        3/3    0/0     2/2      ☢️  │   │               └── syn 2.0.53
0/0        15/15        0/0    0/0     3/3      ☢️  │   │                   ├── proc-macro2 1.0.79
0/0        0/0          0/0    0/0     0/0      ❓  │   │                   ├── quote 1.0.35
0/0        4/4          0/0    0/0     0/0      ☢️  │   │                   └── unicode-ident 1.0.12
0/0        75/121       5/9    0/0     2/4      ☢️  │   ├── once_cell 1.19.0
0/0        5/5          0/0    0/0     0/0      ☢️  │   └── serde 1.0.197
0/0        0/0          0/0    0/0     0/0      🔒  ├── ureq 2.9.6
0/0        0/0          0/0    0/0     0/0      🔒  │   ├── base64 0.21.7
0/0        0/0          0/0    0/0     0/0      ❓  │   ├── cookie 0.18.0
0/0        0/0          0/0    0/0     0/0      🔒  │   │   ├── base64 0.21.7
0/0        8/8          0/0    0/0     0/0      ☢️  │   │   ├── percent-encoding 2.3.1
0/0        9/9          0/0    0/0     0/0      ☢️  │   │   ├── subtle 2.5.0
1/2        223/250      0/0    0/0     4/4      ☢️  │   │   └── time 0.3.34
1/1        5/5          0/0    0/0     1/1      ☢️  │   │       ├── deranged 0.3.11
2/2        29/29        0/0    0/0     0/0      ☢️  │   │       │   ├── powerfmt 0.2.0
0/0        5/5          0/0    0/0     0/0      ☢️  │   │       │   └── serde 1.0.197
0/0        7/7          0/0    0/0     0/0      ☢️  │   │       ├── itoa 1.0.10
1/90       10/582       0/2    0/0     5/63     ☢️  │   │       ├── libc 0.2.153
0/0        0/0          0/0    0/0     0/0      ❓  │   │       ├── num-conv 0.1.0
2/2        29/29        0/0    0/0     0/0      ☢️  │   │       ├── powerfmt 0.2.0
0/0        5/5          0/0    0/0     0/0      ☢️  │   │       ├── serde 1.0.197
0/0        0/0          0/0    0/0     0/0      ❓  │   │       ├── time-core 0.1.2
0/0        0/0          0/0    0/0     0/0      ❓  │   │       └── time-macros 0.2.17
0/0        0/0          0/0    0/0     0/0      ❓  │   │           ├── num-conv 0.1.0
0/0        0/0          0/0    0/0     0/0      ❓  │   │           └── time-core 0.1.2
                                                       │   │   [build-dependencies]
0/0        0/0          0/0    0/0     0/0      ❓  │   │   └── version_check 0.9.4
0/0        0/0          0/0    0/0     0/0      ❓  │   ├── cookie_store 0.21.0
0/0        0/0          0/0    0/0     0/0      ❓  │   │   ├── cookie 0.18.0
0/0        0/0          0/0    0/0     0/0      ❓  │   │   ├── idna 0.5.0
0/0        5/5          0/0    0/0     0/0      ☢️  │   │   │   ├── unicode-bidi 0.3.15
0/0        5/5          0/0    0/0     0/0      ☢️  │   │   │   │   └── serde 1.0.197
0/0        20/20        0/0    0/0     0/0      ☢️  │   │   │   └── unicode-normalization 0.1.23
0/0        0/0          0/0    0/0     0/0      🔒  │   │   │       └── tinyvec 1.6.0
0/0        5/5          0/0    0/0     0/0      ☢️  │   │   │           ├── serde 1.0.197
0/0        0/0          0/0    0/0     0/0      🔒  │   │   │           └── tinyvec_macros 0.1.1
0/0        76/81        1/1    0/0     0/0      ☢️  │   │   ├── indexmap 2.2.5
0/0        0/0          0/0    0/0     0/0      ❓  │   │   │   ├── equivalent 1.0.1
1/1        1443/1622    21/24  1/1     76/88    ☢️  │   │   │   ├── hashbrown 0.14.3
0/0        0/0          0/0    0/0     0/0      ❓  │   │   │   │   ├── equivalent 1.0.1
0/0        5/5          0/0    0/0     0/0      ☢️  │   │   │   │   └── serde 1.0.197
0/0        5/5          0/0    0/0     0/0      ☢️  │   │   │   └── serde 1.0.197
2/2        18/18        1/1    0/0     0/0      ☢️  │   │   ├── log 0.4.21
0/0        5/5          0/0    0/0     0/0      ☢️  │   │   │   └── serde 1.0.197
0/0        5/5          0/0    0/0     0/0      ☢️  │   │   ├── serde 1.0.197
0/0        0/0          0/0    0/0     0/0      ❓  │   │   ├── serde_derive 1.0.197
0/0        4/7          0/0    0/0     0/0      ☢️  │   │   ├── serde_json 1.0.114
0/0        76/81        1/1    0/0     0/0      ☢️  │   │   │   ├── indexmap 2.2.5
0/0        7/7          0/0    0/0     0/0      ☢️  │   │   │   ├── itoa 1.0.10
7/9        579/715      0/0    0/0     2/2      ☢️  │   │   │   ├── ryu 1.0.17
0/0        5/5          0/0    0/0     0/0      ☢️  │   │   │   └── serde 1.0.197
1/2        223/250      0/0    0/0     4/4      ☢️  │   │   ├── time 0.3.34
0/0        0/0          0/0    0/0     0/0      ❓  │   │   └── url 2.5.0
0/0        2/2          0/0    0/0     0/0      ☢️  │   │       ├── form_urlencoded 1.2.1
0/0        8/8          0/0    0/0     0/0      ☢️  │   │       │   └── percent-encoding 2.3.1
0/0        0/0          0/0    0/0     0/0      ❓  │   │       ├── idna 0.5.0
0/0        8/8          0/0    0/0     0/0      ☢️  │   │       ├── percent-encoding 2.3.1
0/0        5/5          0/0    0/0     0/0      ☢️  │   │       └── serde 1.0.197
0/2        13/90        0/2    0/0     0/2      ☢️  │   ├── flate2 1.0.28
5/6        107/155      0/0    0/0     0/0      ☢️  │   │   ├── crc32fast 1.4.0
0/0        0/0          0/0    0/0     0/0      ❓  │   │   │   └── cfg-if 1.0.0
0/0        0/0          0/0    0/0     0/0      🔒  │   │   └── miniz_oxide 0.7.2
0/0        0/0          0/0    0/0     0/0      🔒  │   │       └── adler 1.0.2
2/2        18/18        1/1    0/0     0/0      ☢️  │   ├── log 0.4.21
0/0        75/121       5/9    0/0     2/4      ☢️  │   ├── once_cell 1.19.0
0/0        0/5          0/0    0/0     0/0      🔒  │   ├── rustls 0.22.2
2/2        18/18        1/1    0/0     0/0      ☢️  │   │   ├── log 0.4.21
3/4        377/409      0/0    0/0     1/1      ☢️  │   │   ├── ring 0.17.8
0/0        0/0          0/0    0/0     0/0      ❓  │   │   │   ├── cfg-if 1.0.0
3/7        47/225       0/1    0/0     1/3      ☢️  │   │   │   ├── getrandom 0.2.12
0/0        59/232       2/31   0/0     7/25     ☢️  │   │   │   ├── spin 0.9.8
0/0        0/0          0/0    0/0     0/0      ❓  │   │   │   └── untrusted 0.9.0
                                                       │   │   │   [build-dependencies]
0/0        22/226       0/2    0/0     1/6      ☢️  │   │   │   └── cc 1.0.90
1/90       10/582       0/2    0/0     5/63     ☢️  │   │   │       └── libc 0.2.153
0/0        1/1          0/0    0/0     0/0      ☢️  │   │   ├── rustls-pki-types 1.3.1
0/0        0/0          0/0    0/0     0/0      ❓  │   │   ├── rustls-webpki 0.102.2
3/4        377/409      0/0    0/0     1/1      ☢️  │   │   │   ├── ring 0.17.8
0/0        1/1          0/0    0/0     0/0      ☢️  │   │   │   ├── rustls-pki-types 1.3.1
0/0        0/0          0/0    0/0     0/0      ❓  │   │   │   └── untrusted 0.9.0
0/0        9/9          0/0    0/0     0/0      ☢️  │   │   ├── subtle 2.5.0
1/1        22/22        0/0    0/0     0/0      ☢️  │   │   └── zeroize 1.7.0
0/0        1/1          0/0    0/0     0/0      ☢️  │   ├── rustls-pki-types 1.3.1
0/0        0/0          0/0    0/0     0/0      ❓  │   ├── rustls-webpki 0.102.2
0/0        5/5          0/0    0/0     0/0      ☢️  │   ├── serde 1.0.197
0/0        4/7          0/0    0/0     0/0      ☢️  │   ├── serde_json 1.0.114
0/0        0/0          0/0    0/0     0/0      ❓  │   ├── url 2.5.0
0/0        0/0          0/0    0/0     0/0      🔒  │   └── webpki-roots 0.26.1
0/0        1/1          0/0    0/0     0/0      ☢️  │       └── rustls-pki-types 1.3.1
0/0        0/0          0/0    0/0     0/0      ❓  └── url 2.5.0

27/127     3272/4970    33/76  1/1     105/204

```
# Changelog

- v0.1.0 - Impersonates applin-ios 0.38.0.
