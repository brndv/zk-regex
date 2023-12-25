# zk-regex

This is a library that simplifies circuit building for regex matching. It works alike [halo2-regex](https://github.com/zkemail/halo2-regex), but is different in base halo2 (implemented with [zcash/halo2](https://github.com/zcash/halo2)), a different instance-checking result and corresponding changes in circuit constraints, advice assigning.  [zk-email](https://github.com/zkemail/halo2-zk-email.git) shows how to combine [halo2-regex](https://github.com/zkemail/halo2-regex) with other circuit chips like [zk-email/dynamic-sha2](https://github.com/zkemail/halo2-dynamic-sha256.git), so this lib follows tries to return the same assigned cells information. 

The vrm(Variable-regex mapping) here is almost the same as in  [halo2-regex](https://github.com/zkemail/halo2-regex) .

### Requirements

- rustc 1.68.0-nightly (0468a00ae 2022-12-17)
- • cargo 1.68.0-nightly (cc0a32087 2022-12-14)

### Build

```bash
git clone https://github.com/brndv/zk-regex.git
cd zk-regex
cargo build --release
```

### Test & Example

```bash
cargo test --release test_substr_pass1
cargo test --release test_substr_fail1
cargo run --example regex
```

More tests would be added (tests for single regex matching without public character instance, multiple regex matching) 

### Todo

There are still two unnecessary constraints(lookups) in the lib. The version that removes the constraints is under testing.