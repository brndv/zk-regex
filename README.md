# zk-regex

This is a library that simplifies circuit building for regex matching. It works alike [halo2-regex](https://github.com/zkemail/halo2-regex), but is different in base halo2 (implemented with [zcash/halo2](https://github.com/zcash/halo2)), a different instance-checking result and corresponding changes in circuit constraints, advice assigning.  [zk-email](https://github.com/zkemail/halo2-zk-email.git) shows how to combine [halo2-regex](https://github.com/zkemail/halo2-regex) with other circuit chips like [zk-email/dynamic-sha2](https://github.com/zkemail/halo2-dynamic-sha256.git), so the match_substrs of RegexVerifyConfig(Chip) in this lib tries to return the same kind of assigned cells information. 

The vrm(Variable-regex mapping) here is almost the same as in  [halo2-regex](https://github.com/zkemail/halo2-regex) .
The regex matching(DFA processing) constraints are implemented in RegexVerifyConfig in zk-regex/src/lib.rs, and corresponding advice assigning is within function match_substrs of RegexVerifyConfig.

### Regex Matching circuit table layout

| CharactersInput(Advice) | States(Advice) | SubStrIds(Advice) | MaskedCharacters(Advice) |
| :---------------------- | :------------- | :---------------- | :----------------------- |
|  |  |  |  |


| ValidCharacter(Lookup) | ValidCurrentState(Lookup) | ValidNextState(Lookup) | ValidSubstrId(Lookup) |
| :--------------------- | :------------------------ | :--------------------- | :-------------------- |
|  |  |  |  |

Here is the layout of regex(all string regex and sub-string regex)  matching circuit for a single regex definition from the library (one all string regex comprised of multiple sub-string regex, SubStrIdSum ommitted here for simplicity). Here **MaskedCharacters[row_idx](for instance constraint or assigned from instance)should be equal to CharactersInput[row_idx] times SubStrId[row_idx].**

For matching with multiple regex definitions there should be an array of SubStrId advice columns and SubStrIdSum (row-wise sum of the array of SubStrId advice columns). Then **MaskedCharacters[row_idx] should be equal to CharactersInput[row_idx] times SubStrIdSum[row_idx]**

### Requirements

- rustc 1.68.0-nightly (0468a00ae 2022-12-17)
- cargo 1.68.0-nightly (cc0a32087 2022-12-14)

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

More tests would be added (tests for single regex matching with empty public character instance, multiple regex matching) 

### Todo

The regex circuit implementation could be based on more regex-definition-friendly regex-dfa transformation lib like [regex-dfa](https://github.com/jneem/regex-dfa).