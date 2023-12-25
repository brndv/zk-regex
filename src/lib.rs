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
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Assigned, Circuit, Column, ConstraintSystem, Constraints, Error, Expression,
        Instance, Selector, TableColumn,
    },
    poly::Rotation,
    arithmetic::FieldExt,
};

use log::info;
use std::{
    collections::HashSet,
    fmt::format,
    fs::File,
    io::{BufRead, BufReader},
    marker::PhantomData,
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
    pub masked_characters: Vec<AssignedCell<F,F>>,
    
}

/// Configuration to 1) verify that the input string satisfies the specified regexes and 2) extracts the specified substrings from the input string.
#[derive(Debug, Clone)]
pub struct RegexVerifyConfig<F: FieldExt> {
    characters: Column<Advice>,
    masked_chars: Column<Advice>,   // value of row idx should be equal to characters[idx]*substr_ids_sum[idx]
    substr_ids_sum: Column<Advice>,
    char_enable: Column<Advice>,
    states_array: Vec<Column<Advice>>,
    substr_ids_array: Vec<Column<Advice>>,
    // is_start_array: Vec<Column<Advice>>,
    // is_end_array: Vec<Column<Advice>>,
    start_enable_array: Vec<Column<Advice>>,
    end_enable_array: Vec<Column<Advice>>,
    table_array: Vec<RegexTableConfig<F>>,
    q_first: Selector,
    not_q_first: Selector,
    s_all: Selector,
    //s_masked_chars: Selector,
    //s_substr_ids_sum: Selector,
    max_chars_size: usize,
    /// A vector of regex definitions applied to the input string.
    pub regex_defs: Vec<RegexDefs>,
    //instance_masked_chars: Column<Instance>,
    //instance_substr_id: Column<Instance>,
}

impl<F: FieldExt> RegexVerifyConfig<F> {
    /// Configure a new [`RegexVerifyConfig`].
    ///
    /// # Arguments
    /// * `meta` - a constrain system in which contraints are defined.
    /// * `max_chars_size` - the maximum length of the input string.
    /// * `gate` - a configuration for [`FlexGateConfig`].
    /// * `regex_defs` - a vector of regex definitions applied to the input string.
    ///
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
        
        //let instance_substr_id = meta.instance_column();
        let substr_ids_array = (0..num_regex_def)
            .map(|_| {
                let column = meta.advice_column();
                meta.enable_equality(column);
                column
            })
            .collect::<Vec<Column<Advice>>>();
        // let is_start_array = (0..num_regex_def)
        let start_enable_array = (0..num_regex_def)
            .map(|_| {
                let column = meta.advice_column();
                meta.enable_equality(column);
                column
            })
            .collect::<Vec<Column<Advice>>>();
        // let is_end_array = (0..num_regex_def)
        let end_enable_array = (0..num_regex_def)
            .map(|_| {
                let column = meta.advice_column();
                meta.enable_equality(column);
                column
            })
            .collect::<Vec<Column<Advice>>>();
        let q_first = meta.complex_selector();
        let not_q_first = meta.complex_selector();
        //let s_masked_chars = meta.complex_selector();
        //let s_substr_ids_sum = meta.complex_selector();
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
        
        meta.create_gate("The last enabled state must be accepted state", |meta| {
            let not_q_frist = meta.query_selector(not_q_first);
            let cur_enable = meta.query_advice(char_enable, Rotation::cur());
            //let not_cur_enable = Expression::Constant(F::from(1)) - cur_enable.clone();
            let prev_enable = meta.query_advice(char_enable, Rotation::prev());
            let mut constraints = vec![];
            for (idx, states) in states_array.iter().enumerate() {
                let cur_state = meta.query_advice(*states, Rotation::cur());
                constraints.push(
                    not_q_frist.clone()
                        * ( prev_enable.clone() - cur_enable.clone() )
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
            //lookup start_state of substring
            meta.lookup( |meta| {
                // let enable = meta.query_advice(char_enable, Rotation::cur());
                let states = states_array[idx];
                let substr_ids = substr_ids_array[idx];
                let start_enable = start_enable_array[idx];
                let cur_state = meta.query_advice(states, Rotation::cur());
                let substr_id = meta.query_advice(substr_ids, Rotation::cur());
                let start_enable = meta.query_advice(start_enable, Rotation::cur());
                let dummy_state_val =
                    Expression::Constant(F::from(defs.allstr.largest_state_val + 1));
                let disable = Expression::Constant(F::from(1)) - start_enable.clone();
                vec![
                    (
                        start_enable.clone() * substr_id,
                        table_array[idx].endpoints_substr_ids,
                    ),
                    (
                        start_enable * cur_state + disable * dummy_state_val.clone(),
                        table_array[idx].start_states,
                    ),
                    (dummy_state_val, table_array[idx].end_states),
                ]
            });
            //lookup end_state of substring
            meta.lookup(|meta| {
                // let enable = meta.query_advice(char_enable, Rotation::cur());
                let states = states_array[idx];
                let substr_ids = substr_ids_array[idx];
                // let is_ends = is_end_array[idx];
                let end_enable = end_enable_array[idx];
                let next_state = meta.query_advice(states, Rotation::next());
                let substr_id = meta.query_advice(substr_ids, Rotation::cur());
                let end_enable = meta.query_advice(end_enable, Rotation::cur());
                let dummy_state_val =
                    Expression::Constant(F::from(defs.allstr.largest_state_val + 1));
                // let flag = enable * next_is_end;
                let disable = Expression::Constant(F::from(1)) - end_enable.clone();
                vec![
                    (
                        end_enable.clone() * substr_id,
                        table_array[idx].endpoints_substr_ids,
                    ),
                    (dummy_state_val.clone(), table_array[idx].start_states),
                    (
                        end_enable * next_state + disable * dummy_state_val,
                        table_array[idx].end_states,
                    ),
                ]
            });
        }

        Self {
            characters,
            masked_chars,
            //instance_masked_chars,
            substr_ids_sum,
            //instance_substr_id,
            char_enable,
            states_array,
            substr_ids_array,
            start_enable_array,
            end_enable_array,
            table_array,
            q_first,
            not_q_first,
            s_all,
            //s_masked_chars,
            //s_substr_ids_sum,
            max_chars_size,
            regex_defs,
        }
    }

    /// Verify that the input string `characters` satisfies each regex of [`AllstrRegexDef`] in `regex_defs` and extracts its strings that match any of [`SubstrRegexDef`] in `regex_defs`.
    ///
    /// # Arguments
    /// * `ctx` - a region context.
    /// * `characters` - bytes of the input string.
    ///
    /// # Return values
    /// Return the assigned values as [`AssignedRegexResult`].
    pub fn match_substrs<'v: 'a, 'a>(
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
        let (is_starts, is_ends) = self.derive_is_start_end(&states, &substr_ids);
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
                            let mut is_start_values = is_starts[d_idx][0..characters.len()]
                                .iter()
                                .map(|flag| Value::known(F::from(*flag)))
                                .collect::<Vec<Value<F>>>();
                            let mut is_end_values = is_ends[d_idx][0..characters.len()]
                                .iter()
                                .map(|flag| Value::known(F::from(*flag)))
                                .collect::<Vec<Value<F>>>();
                            for idx in characters.len()..self.max_chars_size {
                                substr_id_values.push(Value::known(F::from(0)));
                                let (state_val, is_start, is_end) = if idx == characters.len() {
                                    (
                                        states[d_idx][idx],
                                        is_starts[d_idx][idx],
                                        is_ends[d_idx][idx],
                                    )
                                } else {
                                    (defs.allstr.largest_state_val + 1, false, false)
                                };
                                state_values.push(Value::known(F::from(state_val)));
                                is_start_values.push(Value::known(F::from(is_start)));
                                is_end_values.push(Value::known(F::from(is_end)));
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
                            for (idx, is_start) in is_start_values.into_iter().enumerate() {
                                region.assign_advice(
                                    || format!("is_start at {} of def {}", idx, d_idx),
                                    self.start_enable_array[d_idx],
                                    idx,
                                    || is_start*enable_values[idx]//start_enable.value().map(|v| *v),
                                )?;
                            }
                
                            for idx in 0..is_end_values.len() - 1 {
                                region.assign_advice(
                                    || format!("is_end at {} of def {}", idx, d_idx),
                                    self.end_enable_array[d_idx],
                                    idx,
                                    || is_end_values[idx + 1]*enable_values[idx],//end_enable.value().map(|v| *v),
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

    /*pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        assigned_masked_chars: &Vec<AssignedCell<F, F>>,
        assigned_substr_ids: &Vec<AssignedCell<F,F>>,
    ) {
        for idx in 0..self.max_chars_size{
            layouter.namespace(|| format!("masked char instance at {}",idx))
                        .constrain_instance(assigned_masked_chars[idx].cell(), self.instance_masked_chars, idx)
                        .unwrap_err();
            layouter.namespace(|| format!("substr id instance at {}",idx))
                        .constrain_instance(assigned_substr_ids[idx].cell(),self.instance_substr_id, idx)
                        .unwrap_err();
        }
        
    }*/

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

    pub(crate) fn derive_is_start_end(
        &self,
        states: &[Vec<u64>],
        substr_ids: &[Vec<usize>],
    ) -> (Vec<Vec<bool>>, Vec<Vec<bool>>) {
        let mut is_starts_array = vec![];
        let mut is_ends_array = vec![];
        let mut substr_id_offset = 1usize;
        for (d_idx, defs) in self.regex_defs.iter().enumerate() {
            let state_len = states[d_idx].len();
            let mut is_starts = states[d_idx][0..state_len - 1]
                .iter()
                .zip(substr_ids[d_idx].iter())
                .map(|(state, substr_id)| {
                    if *substr_id == 0 {
                        return false;
                    }
                    let substr_idx = *substr_id - substr_id_offset;
                    let valid_start_states = &defs.substrs[substr_idx].start_states;
                    valid_start_states.contains(state)
                })
                .collect::<Vec<bool>>();
            is_starts.push(false);
            let is_ends = states[d_idx][1..]
                .iter()
                .zip(substr_ids[d_idx].iter())
                .map(|(state, substr_id)| {
                    if *substr_id == 0 {
                        return false;
                    }
                    let substr_idx: usize = *substr_id - substr_id_offset;
                    let valid_end_states = &defs.substrs[substr_idx].end_states;
                    valid_end_states.contains(state)
                })
                .collect::<Vec<bool>>();
            let is_ends = vec![&vec![false][..], &is_ends].concat();
            is_starts_array.push(is_starts);
            is_ends_array.push(is_ends);
            substr_id_offset += defs.substrs.len();
        }
        (is_starts_array, is_ends_array)
    }
}

#[cfg(feature = "vrm")]
#[cfg(test)]
mod test {
    use halo2_proofs::{
        arithmetic::FieldExt, 
        dev::MockProver,
        circuit::{Layouter, Chip, Value, AssignedCell, Region, SimpleFloorPlanner}, 
        plonk::{Column, Advice, Instance, Error, Selector, ConstraintSystem, Circuit, Expression, create_proof, keygen_vk, keygen_pk, ProvingKey, VerifyingKey, verify_proof, SingleVerifier}, 
        poly::{Rotation, commitment::Params}, 
        pasta::{Fp, EqAffine}, transcript::{Blake2bWrite, Challenge255, Blake2bRead}, 
    };
    

    use super::*;
    use crate::{
        defs::{AllstrRegexDef, SubstrRegexDef},
        vrm::DecomposedRegexConfig,
    };

    //use halo2_proofs::poly::kzg::multiopen::{ProverGWC, VerifierGWC};
    use rand_core::OsRng;
    use std::marker::PhantomData;
    use std::{collections::HashSet, path::Path};

    use super::*;

    use itertools::Itertools;

    // Checks a regex of string len
    const MAX_STRING_LEN: usize = 128;
    const K: usize = 17;
    
    #[derive(Clone, Debug)]
    pub struct TestConfig<F: FieldExt> {
        inner: RegexVerifyConfig<F>,
        // Masked Characters Instance
        masked_str_instance: Column<Instance>,
        // Substrid Instance
        substr_ids_instance: Column<Instance>,
    }

    #[derive(Default, Clone, Debug)]
    struct TestCircuit1<F: FieldExt> {
        // Since this is only relevant for the witness, we can opt to make this whatever convenient type we want
        characters: Vec<u8>,
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt> Circuit<F> for TestCircuit1<F> {
        type Config = TestConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        // Circuit without witnesses, called only during key generation
        fn without_witnesses(&self) -> Self {
            Self {
                characters: vec![],
                _marker: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let all_regex_def1 =
                AllstrRegexDef::read_from_text("./test_regexes/regex1_test_lookup.txt");
            let substr_def1 =
                SubstrRegexDef::read_from_text("./test_regexes/substr1_test_lookup.txt");
            let all_regex_def2 =
                AllstrRegexDef::read_from_text("./test_regexes/regex2_test_lookup.txt");
            let substr_def2 =
                SubstrRegexDef::read_from_text("./test_regexes/substr2_test_lookup.txt");
            
            let regex_defs = vec![
                RegexDefs {
                    allstr: all_regex_def1,
                    substrs: vec![substr_def1],
                },
                RegexDefs {
                    allstr: all_regex_def2,
                    substrs: vec![substr_def2],
                },
            ];
            let inner = RegexVerifyConfig::configure(meta, MAX_STRING_LEN, regex_defs);
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
            let regex1_decomposed: DecomposedRegexConfig =
                serde_json::from_reader(File::open("./test_regexes/regex1_test.json").unwrap())
                    .unwrap();
            regex1_decomposed
                .gen_regex_files(
                    &Path::new("./test_regexes/regex1_test_lookup.txt").to_path_buf(),
                    &[Path::new("./test_regexes/substr1_test_lookup.txt").to_path_buf()],
                )
                .unwrap();
            let regex2_decomposed: DecomposedRegexConfig =
                serde_json::from_reader(File::open("./test_regexes/regex2_test.json").unwrap())
                    .unwrap();
            regex2_decomposed
                .gen_regex_files(
                    &Path::new("./test_regexes/regex2_test_lookup.txt").to_path_buf(),
                    &[Path::new("./test_regexes/substr2_test_lookup.txt").to_path_buf()],
                )
                .unwrap();

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

    #[test]
    fn test_substr_pass1() {
        let characters: Vec<u8> = "email was meant for @y. Also for x."
            .chars()
            .map(|c| c as u8)
            .collect();
        // Make a vector of the numbers 1...24
        // let states = (1..=STRING_LEN as u128).collect::<Vec<u128>>();
        // assert_eq!(characters.len(), STRING_LEN);
        // assert_eq!(states.len(), STRING_LEN);

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

        // Make a vector of the numbers 1...24
        // let states = (1..=STRING_LEN as u128).collect::<Vec<u128>>();
        // assert_eq!(characters.len(), STRING_LEN);
        // assert_eq!(states.len(), STRING_LEN);

        // Successful cases
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
    
}
