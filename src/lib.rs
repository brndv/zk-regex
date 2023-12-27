/// Regex definitions.
pub mod defs;
/// Lookup table for each regex definition.
pub mod table;
/// Variable-regex mapping, a helpful tool to generate regex definition files from decomposed regexes.
#[cfg(feature = "vrm")]
pub mod vrm;
use crate::table::RegexTableConfig;
use crate::{AllstrRegexDef, RegexDefs, SubstrRegexDef};
pub use defs::*;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression,
        Selector, 
    },
    poly::Rotation,
    arithmetic::FieldExt,
};

#[cfg(feature = "vrm")]
use vrm::DecomposedRegexConfig;

/// Output type definition of [`RegexVerifyConfig`].
#[derive(Debug, Clone, Default)]
pub struct RegexAssignedResult<F: FieldExt> {
    /// The assigned bits of `enable_flag` that indicates whether each character of the input string is a padded byte or not. (`enable_flag=true` iff the character is not padded one.)
    /// The length is equal to `max_chars_size`.
    pub all_enable_flags: Vec<AssignedCell<F, F>>,
    /// The assigned character (byte) of the input string.
    /// The length is equal to `max_chars_size`.
    pub all_characters: Vec<AssignedCell<F, F>>,
    /// The assigned substring id of characters in the input string.
    /// The length is equal to `max_chars_size`.    
    pub masked_substr_ids: Vec<AssignedCell<F, F>>,
    /// The assigned masked characters
    /// masked_characters[idx] should be equal to allcharacters[idx]*masked_substr_ids[idx]
    pub masked_characters: Vec<AssignedCell<F,F>>,
    
}

/// Configuration to 
/// 1) verify that the input string satisfies the specified regexes 
/// 2) the specified regex substrings from the input string times with corresponding subregex ids for further instance contraints
#[derive(Debug, Clone)]
pub struct RegexVerifyConfig<F: FieldExt> {
    characters: Column<Advice>,      // characters input to match 
    masked_chars: Column<Advice>,   // value of masked_chars[idx] should be equal to characters[idx]*substr_ids_sum[idx]
    substr_ids_sum: Column<Advice>,     // row-wise sum of substr_ids_array, or substr_ids_sum[idx] = sum{substr_ids_array[col][idx]|col=0..columns_num} 
    char_enable: Column<Advice>,             // enabled characters
    states_array: Vec<Column<Advice>>,      // states series of DFA processing the input characters         
    substr_ids_array: Vec<Column<Advice>>,   // character[idx] belongs to which public sub-regex of which regex definitions
    table_array: Vec<RegexTableConfig<F>>,  // DFA transition table arrays for the array of regexes for matching
    q_first: Selector,            // first row selector
    not_q_first: Selector,       // selector for all rows except the first   
    s_all: Selector,            // all rows selector
    max_chars_size: usize,     // largest length of input characters allowed for matching  
    pub regex_defs: Vec<RegexDefs>,   // regex definitions for matching
}

impl<F: FieldExt> RegexVerifyConfig<F> {
    /// Configure a new [`RegexVerifyConfig`].
    /// # Return values
    /// Return a new [`RegexVerifyConfig`].
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        max_chars_size: usize,
        regex_defs: Vec<RegexDefs>,
    ) -> Self {
        let num_regex_def = regex_defs.len();
        let characters = meta.advice_column();
        let masked_chars = meta.advice_column();
        let char_enable = meta.advice_column();
        let substr_ids_sum = meta.advice_column();
        meta.enable_equality(masked_chars);
        meta.enable_equality(substr_ids_sum);
        
        let states_array = (0..num_regex_def)
            .map(|_| {
                let column = meta.advice_column();
                meta.enable_equality(column);
                column
            })
            .collect::<Vec<Column<Advice>>>();
        
        let substr_ids_array = (0..num_regex_def)
            .map(|_| {
                let column = meta.advice_column();
                meta.enable_equality(column);
                column
            })
            .collect::<Vec<Column<Advice>>>();
        
        let q_first = meta.complex_selector();
        let not_q_first = meta.complex_selector();
        
        let s_all = meta.complex_selector();
        let table_array = (0..num_regex_def)
            .map(|_| RegexTableConfig::configure(meta))
            .collect::<Vec<RegexTableConfig<F>>>();
        meta.enable_equality(characters);
        meta.enable_equality(char_enable);

        meta.create_gate("The state must start from the first state value", |meta| {
            let q_frist = meta.query_selector(q_first);
            let cur_enable = meta.query_advice(char_enable, Rotation::cur());
            let not_cur_enable = Expression::Constant(F::from(1)) - cur_enable.clone();
            let mut constraints =
                vec![q_frist.clone() * cur_enable.clone() * not_cur_enable.clone()];
            for (idx, states) in states_array.iter().enumerate() {
                let cur_state = meta.query_advice(*states, Rotation::cur());
                constraints.push(
                    q_frist.clone()
                        * cur_enable.clone()
                        * (cur_state
                            - Expression::Constant(F::from(regex_defs[idx].allstr.first_state_val))),
                );
            }
            constraints
        });
        
        meta.create_gate("The last enabled state must be the accepted state", |meta| {
            let not_q_frist = meta.query_selector(not_q_first);
            let cur_enable = meta.query_advice(char_enable, Rotation::cur());
            //let not_cur_enable = Expression::Constant(F::from(1)) - cur_enable.clone();
            let prev_enable = meta.query_advice(char_enable, Rotation::prev());
            let mut constraints = vec![];
            for (idx, states) in states_array.iter().enumerate() {
                let cur_state = meta.query_advice(*states, Rotation::cur());
                constraints.push(
                    not_q_frist.clone()
                        * ( prev_enable.clone() - cur_enable.clone() )   // enable change
                        * ( cur_state
                            - Expression::Constant(F::from(regex_defs[idx].allstr.accepted_state_val))),
                );
            }
            constraints
        });
        

        meta.create_gate("The transition of enable flags", |meta| {
            let not_q_frist = meta.query_selector(not_q_first);
            let cur_enable = meta.query_advice(char_enable, Rotation::cur());
            let not_cur_enable = Expression::Constant(F::from(1)) - cur_enable.clone();
            let prev_enable = meta.query_advice(char_enable, Rotation::prev());
            let enable_change = prev_enable.clone() - cur_enable.clone();
            let not_enable_change = Expression::Constant(F::from(1)) - enable_change.clone();
            vec![
                not_q_frist.clone() * enable_change * not_enable_change,
                not_q_frist * cur_enable * not_cur_enable,
            ]
        });
        
        meta.create_gate("row-wise sums of substr_ids from all all-string regex", |meta| {
            let sub_ids_sum = (0..regex_defs.len())
                                .map(|i| meta.query_advice(substr_ids_array[i], Rotation::cur()))
                                .fold(Expression::Constant(F::from(0)), |acc,e| acc+e);
            let cur_sub_ids_sum = meta.query_advice(substr_ids_sum, Rotation::cur());
            let s_all = meta.query_selector(s_all);
            vec![s_all * ( cur_sub_ids_sum - sub_ids_sum )]
        });

        meta.create_gate("masked characters(character value times substr_ids_sum) that match instance", 
        |meta| {
            let cur_masked_char = meta.query_advice(masked_chars, Rotation::cur());
            let cur_char = meta.query_advice(characters, Rotation::cur());
            let cur_substrid_sum = meta.query_advice(substr_ids_sum, Rotation::cur());
            let s_all = meta.query_selector(s_all);

            vec![s_all  * ( cur_masked_char - cur_char * cur_substrid_sum)]
        });

        for (idx, defs) in regex_defs.iter().enumerate() {
            //"lookup characters and their state", 
            meta.lookup(|meta| {
                let enable = meta.query_advice(char_enable, Rotation::cur());
                let not_enable = Expression::Constant(F::from(1)) - enable.clone();
                let character = meta.query_advice(characters, Rotation::cur());
                let states = states_array[idx];
                let substr_ids = substr_ids_array[idx];
                let cur_state = meta.query_advice(states, Rotation::cur());
                let next_state = meta.query_advice(states, Rotation::next());
                let substr_id = meta.query_advice(substr_ids, Rotation::cur());
                let dummy_state_val =
                    Expression::Constant(F::from(defs.allstr.largest_state_val + 1));
                vec![
                    (
                        enable.clone() * character.clone(),
                        table_array[idx].characters,
                    ),
                    (
                        enable.clone() * cur_state + not_enable.clone() * dummy_state_val.clone(),
                        table_array[idx].cur_states,
                    ),
                    (
                        enable.clone() * next_state + not_enable.clone() * dummy_state_val.clone(),
                        table_array[idx].next_states,
                    ),
                    (enable.clone() * substr_id, table_array[idx].substr_ids),
                ]
            });
        }

        Self {
            characters,
            masked_chars,
            substr_ids_sum,
            char_enable,
            states_array,
            substr_ids_array,
            table_array,
            q_first,
            not_q_first,
            s_all,
            max_chars_size,
            regex_defs,
        }
    }

    /// Verify that the input string `characters` satisfies each regex of [`AllstrRegexDef`] in `regex_defs` and extracts its strings that match any of [`SubstrRegexDef`] in `regex_defs`.
    ///
    /// # Return values
    /// Return the assigned values as [`RegexAssignedResult`].
    pub fn match_substrs(
        &self,
        mut layouter: impl Layouter<F>,
        characters: &[u8],
    ) -> Result<RegexAssignedResult<F>, Error> {
        
        let states = self.derive_states(characters);
        let substr_ids = self.derive_substr_ids(states.as_slice());

        let mut substr_ids_sum = (0..substr_ids[0].len())
                                            .map(|i| {
                                                let mut sum = 0;
                                                for j in 0..substr_ids.len() {
                                                    sum += substr_ids[j][i];
                                                }
                                                sum
                                            }).collect::<Vec<usize>>();
        let mut enable_values = vec![];
        let mut character_values = vec![];
        for char in characters.iter() {
            enable_values.push(Value::known(F::from(1)));
            character_values.push(Value::known(F::from(*char as u64)));
        }
        for _ in characters.len()..self.max_chars_size {
            enable_values.push(Value::known(F::from(0)));
            character_values.push(Value::known(F::from(0)));
            substr_ids_sum.push(0);
        }
        
        layouter.assign_region(|| "all regex matching",
        |mut region| {
                        self.q_first.enable(&mut region,0)?;
                        for idx in 1..self.max_chars_size {
                            self.not_q_first.enable(&mut region, idx)?;
                        }
                        for idx in 0..self.max_chars_size {
                            self.s_all.enable(&mut region, idx)?;
                        }
                        let assigned_enables = enable_values.clone()
                            .into_iter()
                            .enumerate()
                            .map(|(idx, val)| {
                                let assigned = region.assign_advice(
                                    || format!("enable at {}", idx),
                                    self.char_enable,
                                    idx,
                                    || val,
                                ).unwrap();
                                assigned
                            })
                            .collect::<Vec<AssignedCell<F,F>>>();
                        let assigned_characters = character_values.clone()
                            .into_iter()
                            .enumerate()
                            .map(|(idx, val)| {
                                let assigned = region.assign_advice(
                                    || format!("character at {}", idx),
                                    self.characters,
                                    idx,
                                    || val,
                                ).unwrap();
                                assigned
                            })
                            .collect::<Vec<AssignedCell<F,F>>>();
                        let assigned_masked_subtr_ids = substr_ids_sum.clone()
                            .into_iter()
                            .enumerate()
                            .map(|(idx, val)| {
                                region.assign_advice(
                                    || format!("character at {}", idx),
                                    self.substr_ids_sum,
                                    idx,
                                    || Value::known(F::from(val as u64)),
                                ).unwrap()
                            })
                            .collect::<Vec<AssignedCell<F,F>>>();
                        let assigned_masked_characters = character_values.clone()
                            .into_iter()
                            .enumerate()
                            .map(|(idx, val)| {
                                let masked_char_cell = region.assign_advice(
                                    || format!("masked character at {}", idx),
                                    self.masked_chars,
                                    idx,
                                    || val * Value::known(F::from(substr_ids_sum[idx] as u64))
                                ).unwrap();
                                masked_char_cell
                            })
                            .collect::<Vec<AssignedCell<F,F>>>();
                        for (d_idx, defs) in self.regex_defs.iter().enumerate() {
                            let mut state_values = states[d_idx][0..characters.len()]
                            .iter()
                            .map(|state| Value::known(F::from(*state)))
                            .collect::<Vec<Value<F>>>();
                            let mut substr_id_values = substr_ids[d_idx]
                                .iter()
                                .map(|substr_id| Value::known(F::from(*substr_id as u64)))
                                .collect::<Vec<Value<F>>>();
                        
                            for idx in characters.len()..self.max_chars_size {
                                substr_id_values.push(Value::known(F::from(0)));
                                let state_val = if idx == characters.len() {
                                    states[d_idx][idx]
                                } else {
                                    defs.allstr.largest_state_val + 1
                                };
                                state_values.push(Value::known(F::from(state_val)));
                                
                            }
                            for (s_idx, state) in state_values.into_iter().enumerate() {
                                region.assign_advice(
                                    || format!("state at {} of def {}", s_idx, d_idx),
                                    self.states_array[d_idx],
                                    s_idx,
                                    || state,
                                )?;
                            }
                            for (s_idx, substr_id) in substr_id_values.into_iter().enumerate() {
                                region.assign_advice(
                                    || format!("substr_id at {} of def {}", s_idx, d_idx),
                                    self.substr_ids_array[d_idx],
                                    s_idx,
                                    || substr_id,
                                )?;
                            }
                            

                        }
                    let result = RegexAssignedResult {
                        all_characters: assigned_characters,
                        all_enable_flags: assigned_enables,
                        masked_substr_ids: assigned_masked_subtr_ids,
                        masked_characters: assigned_masked_characters,
                    };
                    Ok(result)
            },
        )

    }

    /// Load looup tables of each [`RegexDefs`] in `regex_defs`.
    ///
    /// # Arguments
    /// * `layouter` - a [`Layouter`] in which the lookup tables are loaded.
    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let mut substr_id_offset = 1;
        for (idx, table) in self.table_array.iter().enumerate() {
            substr_id_offset = table.load(layouter, &self.regex_defs[idx], substr_id_offset)?;
        }
        Ok(())
    }

    pub(crate) fn derive_states(&self, characters: &[u8]) -> Vec<Vec<u64>> {
        let mut states = vec![];
        for (d_idx, defs) in self.regex_defs.iter().enumerate() {
            states.push(vec![defs.allstr.first_state_val]);
            for (c_idx, char) in characters.into_iter().enumerate() {
                let state = states[d_idx][c_idx];
                let next_state = defs.allstr.state_lookup.get(&(*char, state));
                
                match next_state {
                    Some((_, s)) => states[d_idx].push(*s),
                    None => panic!("The transition from {} by {} is invalid!", state, *char),
                }
            }
            assert_eq!(states[d_idx].len(), characters.len() + 1);
        }
        states
    }

    pub(crate) fn derive_substr_ids(&self, states: &[Vec<u64>]) -> Vec<Vec<usize>> {
        let mut substr_ids: Vec<Vec<usize>> = vec![];
        let mut substr_id_offset = 1;
        for (d_idx, defs) in self.regex_defs.iter().enumerate() {
            substr_ids.push(vec![0; states[d_idx].len() - 1]);
            for state_idx in 0..(states[d_idx].len() - 1) {
                for (substr_idx, substr_def) in defs.substrs.iter().enumerate() {
                    if substr_def
                        .valid_state_transitions
                        .get(&(states[d_idx][state_idx], states[d_idx][state_idx + 1]))
                        .is_some()
                    {
                        substr_ids[d_idx][state_idx] = substr_id_offset + substr_idx;
                        break;
                    }
                }
            }
            substr_id_offset += defs.substrs.len();
        }
        substr_ids
    }
    
}

#[cfg(feature = "vrm")]
#[cfg(test)]
mod test {
    use halo2_proofs::{
        arithmetic::FieldExt, 
        dev::MockProver,
        circuit::{Layouter, SimpleFloorPlanner}, 
        plonk::{Column, Instance, Error, ConstraintSystem, Circuit},  
        pasta::Fp,
    };
    
    use super::*;
    use crate::{
        defs::{AllstrRegexDef, SubstrRegexDef},
        vrm::DecomposedRegexConfig,
    };

    use std::marker::PhantomData;
    use std::{path::Path,fs::File};

    // Checks a regex of string len
    const MAX_STRING_LEN: usize = 128;
    const K: usize = 12;

    #[macro_export]
    macro_rules! impl_regex_circuit{
        ($config_name: ident, $circuit_name: ident, $regex_defs: expr, $max_str_len: expr) =>{
            #[derive(Clone, Debug)]
            pub struct $config_name<F: FieldExt> {
                inner: RegexVerifyConfig<F>,
                // Masked Characters Instance
                masked_str_instance: Column<Instance>,
                // Substrid Instance
                substr_ids_instance: Column<Instance>,
            }

            #[derive(Default, Clone, Debug)]
            struct $circuit_name<F: FieldExt> {
                characters: Vec<u8>,
                _marker: PhantomData<F>,
            }

            impl<F: FieldExt> Circuit<F> for $circuit_name<F> {
                type Config = $config_name<F>;
                type FloorPlanner = SimpleFloorPlanner;

                // Circuit without witnesses, called only during key generation
                fn without_witnesses(&self) -> Self {
                    Self {
                        characters: vec![],
                        _marker: PhantomData,
                    }
                }

                fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                    let regex_defs = $regex_defs;
                    let inner = RegexVerifyConfig::configure(meta, $max_str_len, regex_defs);
                    let masked_str_instance = meta.instance_column();
                    let substr_ids_instance = meta.instance_column();
                    meta.enable_equality(masked_str_instance);
                    meta.enable_equality(substr_ids_instance);
                    Self::Config{
                        inner,
                        masked_str_instance,
                        substr_ids_instance,
                    }
                }

                fn synthesize(
                    &self,
                    config: Self::Config,
                    mut layouter: impl Layouter<F>,
                ) -> Result<(), Error> {

                    config.inner.load(&mut layouter)?;
                    
                    let result = config.inner.match_substrs(layouter.namespace(|| "match regex substr"), &self.characters).unwrap();
                    
                    for idx in 0..MAX_STRING_LEN {
                        layouter.namespace(|| format!("masked str instance at {:}",idx))
                            .constrain_instance(result.masked_characters[idx].cell(), config.masked_str_instance, idx)?;
                        layouter.namespace(|| format!("substr ids instance at {:}",idx))
                            .constrain_instance(result.masked_substr_ids[idx].cell(), config.substr_ids_instance, idx)?;  
                    }
                    
                    Ok(())
                }
            }

        }
    }
    
    impl_regex_circuit!(
        TestConfig1,
        TestCircuit1,
        vec![
            RegexDefs{
                allstr: AllstrRegexDef::read_from_text("./test_regexes/regex1_test_lookup.txt"),
                substrs: vec![SubstrRegexDef::read_from_text("./test_regexes/substr1_test_lookup.txt")],
            },
            RegexDefs{
                allstr: AllstrRegexDef::read_from_text("./test_regexes/regex2_test_lookup.txt"),
                substrs: vec![SubstrRegexDef::read_from_text("./test_regexes/substr2_test_lookup.txt")],
            }
        ],
        128
    );

    impl_regex_circuit!(
        TestConfig2,
        TestCircuit2,
        vec![
            RegexDefs{
                allstr: AllstrRegexDef::read_from_text("./test_regexes/regex4_test_lookup.txt"),
                substrs: vec![],
            }
        ],
        128
    );

    #[test]
    fn test_substr_pass1() {
        let characters: Vec<u8> = "email was meant for @y. Also for x."
            .chars()
            .map(|c| c as u8)
            .collect();

        // Successful cases
        let circuit = TestCircuit1::<Fp> {
            characters,
            _marker: PhantomData,
        };
        let correct_substrs = vec![(21, "y".to_string()), (33, "x".to_string())];
        let mut expected_masked_chars = vec![Fp::from(0);MAX_STRING_LEN];
        let mut expected_substr_ids = vec![Fp::from(0);MAX_STRING_LEN];
        for (substr_idx, (start, chars)) in correct_substrs.iter().enumerate() {
            for (idx, char) in chars.as_bytes().iter().enumerate() {
                expected_substr_ids[start + idx] = Fp::from((substr_idx + 1) as u64);
                expected_masked_chars[start + idx] = Fp::from(*char as u64)*Fp::from((substr_idx + 1) as u64);
            }
        }
        let prover = MockProver::run(K as u32, &circuit, vec![expected_masked_chars,expected_substr_ids]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_substr_fail1() {
        // 1. The string does not satisfy the regex.
        let characters: Vec<u8> = "email was meant for @@".chars().map(|c| c as u8).collect();

        // failure cases
        let circuit = TestCircuit1::<Fp> {
            characters,
            _marker: PhantomData,
        };
        let correct_substrs :Vec<(usize,String)> = vec![];
        let mut expected_masked_chars = vec![Fp::from(0);MAX_STRING_LEN];
        let mut expected_substr_ids = vec![Fp::from(0);MAX_STRING_LEN];
        for (substr_idx, (start, chars)) in correct_substrs.iter().enumerate() {
            for (idx, char) in chars.as_bytes().iter().enumerate() {
                expected_substr_ids[start + idx] = Fp::from((substr_idx + 1) as u64);
                expected_masked_chars[start + idx] = Fp::from(*char as u64)*Fp::from((substr_idx + 1) as u64);
            }
        }

        let prover = MockProver::run(K as u32, &circuit, vec![expected_masked_chars,expected_substr_ids]).unwrap();
        match prover.verify() {
            Err(_) => {
                println!("Error successfully achieved!");
            }
            _ => assert!(false, "Should be error."),
        }
    }

    #[test]
    fn test_single_regex_match_pass(){
        let regex1_decomposed: DecomposedRegexConfig =
                serde_json::from_reader(File::open("./test_regexes/regex4_test.json").unwrap())
                    .unwrap();
        regex1_decomposed
            .gen_regex_files(
                &Path::new("./test_regexes/regex4_test_lookup.txt").to_path_buf(),
                &[],
            )
            .unwrap();

        let characters: Vec<u8> = "abcca32@ab.xyz aca3ca@bc.com"
            .chars()
            .map(|c| c as u8)
            .collect();

        // Successful cases
        let circuit = TestCircuit2::<Fp> {
            characters,
            _marker: PhantomData,
        };
        let correct_substrs : Vec<(usize,String)> = vec![];
        let mut expected_masked_chars = vec![Fp::from(0);MAX_STRING_LEN];
        let mut expected_substr_ids = vec![Fp::from(0);MAX_STRING_LEN];
        for (substr_idx, (start, chars)) in correct_substrs.iter().enumerate() {
            for (idx, char) in chars.as_bytes().iter().enumerate() {
                expected_substr_ids[start + idx] = Fp::from((substr_idx + 1) as u64);
                expected_masked_chars[start + idx] = Fp::from(*char as u64)*Fp::from((substr_idx + 1) as u64);
            }
        }
        let prover = MockProver::run(K as u32, &circuit, vec![expected_masked_chars,expected_substr_ids]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
    
}
