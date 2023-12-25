use std::{
    marker::PhantomData,
    path::Path,
    fs::File
};
use halo2_proofs::{
    arithmetic::FieldExt, 
    dev::MockProver,
    circuit::{Layouter, Chip, Value, AssignedCell, Region, SimpleFloorPlanner}, 
    plonk::{Column, Advice, Instance, Error, Selector, ConstraintSystem, Circuit, Expression, create_proof, keygen_vk, keygen_pk, ProvingKey, VerifyingKey, verify_proof, SingleVerifier}, 
    poly::{Rotation, commitment::Params}, 
    pasta::{Fp, EqAffine}, transcript::{Blake2bWrite, Challenge255, Blake2bRead}, 
};
use rand_core::OsRng;




use zk_regex::{
    defs::{AllstrRegexDef, RegexDefs, SubstrRegexDef},
    RegexVerifyConfig,
    vrm::DecomposedRegexConfig,
};



use fancy_regex::Regex;
use itertools::Itertools;

pub const MAX_STRING_LEN: usize = 128;
pub const K: usize = 14;

/// 1. Define a configure of our example circuit.
#[derive(Clone, Debug)]
pub struct ExampleConfig<F: FieldExt> {
    inner: RegexVerifyConfig<F>,
    // Masked Characters Instance
    masked_str_instance: Column<Instance>,
    // Substrid Instance
    substr_ids_instance: Column<Instance>,
}

/// 2. Define an example circuit.
#[derive(Default, Clone, Debug)]
pub struct RegexCircuit<F: FieldExt> {
    // The bytes of the input string.
    characters: Vec<u8>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> RegexCircuit<F> {
    /// The number of advice columns in [`FlexGateConfig`].
    const NUM_ADVICE: usize = 2;
    /// The number of fix columns in [`FlexGateConfig`].
    const NUM_FIXED: usize = 1;
    /// Path to save all string regex DFA transition table
    const ALLSTR_PATH: &str = "./examples/ex_allstr.txt";
}

impl<F: FieldExt> Circuit<F> for RegexCircuit<F> {
    type Config = ExampleConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    // Circuit without witnesses, called only during key generation
    fn without_witnesses(&self) -> Self {
        Self {
            characters: vec![],
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let all_regex_def1 = AllstrRegexDef::read_from_text(Self::ALLSTR_PATH);
        let substr_defs = ["./examples/ex_substr_id1.txt"].into_iter()
                            .map(|path| 
                                SubstrRegexDef::read_from_text(path)
                            ).collect();
        
        let regex_defs = vec![RegexDefs {
            allstr: all_regex_def1,
            substrs: substr_defs,
        }];
        let inner = RegexVerifyConfig::configure(meta, MAX_STRING_LEN, regex_defs);
        let masked_str_instance = meta.instance_column();
        meta.enable_equality(masked_str_instance);
        let substr_ids_instance = meta.instance_column();
        meta.enable_equality(substr_ids_instance);
        Self::Config { inner, masked_str_instance, substr_ids_instance}
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {

        config.inner.load(&mut layouter)?;
        
        let result = config.inner.match_substrs(layouter.namespace(|| "match regex substr"), &self.characters)?;
        
        for idx in 0..MAX_STRING_LEN {
            layouter.namespace(|| format!("masked str instance at {:}",idx))
                .constrain_instance(result.masked_characters[idx].cell(), config.masked_str_instance, idx)?;
            layouter.namespace(|| format!("substr ids instance at {:}",idx))
                .constrain_instance(result.masked_substr_ids[idx].cell(), config.substr_ids_instance, idx)?;  
        }
        Ok(())
    }
}

pub fn create_circuit(characters: Vec<u8>) -> RegexCircuit<Fp> {
    RegexCircuit::<Fp> {
        characters,
        _marker: PhantomData,
    }
}

// Draws the layout of the circuit. Super useful for debugging.
#[cfg(not(target_family = "wasm"))]
pub fn draw_circuit<F: FieldExt>(k: u32, circuit: &RegexCircuit<F>) {
    use plotters::prelude::*;
    let base = BitMapBackend::new("./examples/layout.png", (1600,1600)).into_drawing_area();
    base.fill(&WHITE).unwrap();
    let base = base.titled("Substring Regex Matching Circuit", ("sans-serif", 24)).unwrap();

    halo2_proofs::dev::CircuitLayout::default()
        .show_equality_constraints(true)
        .render(k, circuit, &base)
        .unwrap();
}



pub fn get_substr(input_str: &str, regexes: &[String]) -> Option<(usize, String)> {
    let regexes = regexes
        .into_iter()
        .map(|raw| Regex::new(&raw).unwrap())
        .collect_vec();
    let mut start = 0;
    let mut substr = input_str;

    for regex in regexes.into_iter() {
        // println!(r"regex {}", regex);
        match regex.find(substr).unwrap() {
            Some(m) => {
                start += m.start();
                substr = m.as_str();
            }
            None => {
                return None;
            }
        };
    }
    Some((start, substr.to_string()))
}

pub fn gen_masked_instance(text :&str) -> (Vec<Fp>,Vec<Fp>){
    let mut expected_masked_chars = vec![Fp::from(0); MAX_STRING_LEN];
    let mut expected_substr_ids = vec![Fp::from(0); MAX_STRING_LEN];
    let correct_substrs = vec![
        get_substr(&text, &[r"(?<=from:).*@.*(?=to)".to_string(), "<?(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z|0|1|2|3|4|5|6|7|8|9|_|\\.|-)+@(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z|0|1|2|3|4|5|6|7|8|9|_|\\.|-)+>?".to_string(), "(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z|0|1|2|3|4|5|6|7|8|9|_|\\.|-)+@(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z|0|1|2|3|4|5|6|7|8|9|_|\\.|-)+".to_string()]).unwrap(),
    ];

    println!("Matched sub-strings(public:true):{:?}",correct_substrs);

    for (substr_idx, (start, chars)) in correct_substrs.iter().enumerate() {
        for (idx, char) in chars.as_bytes().iter().enumerate() {
            expected_substr_ids[start + idx] = Fp::from((substr_idx + 1) as u64);
            expected_masked_chars[start + idx] = Fp::from(*char as u64)*Fp::from((substr_idx + 1) as u64);
        }
    }
    (expected_masked_chars,expected_substr_ids)
}



// Generates setup parameters using k, which is the number of rows of the circuit
// can fit in and must be a power of two
pub fn generate_setup_params(
    k: u32,
) -> Params<EqAffine>{
    Params::<EqAffine>::new(k)
}

// Generates the verifying and proving keys. We can pass in an empty circuit to generate these
pub fn generate_keys(
    params: &Params<EqAffine>,
    emp_circuit: &RegexCircuit<Fp>,
) -> (ProvingKey<EqAffine>, VerifyingKey<EqAffine>) {
    // just to emphasize that for vk, pk we don't need to know the value of `x`
    let vk = keygen_vk(params, emp_circuit).unwrap();
    let pk = keygen_pk(params, vk.clone(), emp_circuit).unwrap();
    (pk, vk)
}

// Runs the mock prover and prints any errors
pub fn run_mock_prover(
    k: u32,
    circuit: &RegexCircuit<Fp>,
    masked_chars: &Vec<Fp>,
    masked_substr_ids: &Vec<Fp>,
) {
    let prover = MockProver::run(k, circuit, vec![masked_chars.clone(),masked_substr_ids.clone()]).expect("Mock prover should run");
    let res = prover.verify();
    match res {
        Ok(()) => println!("MockProver OK"),
        Err(e) => println!("err {:#?}", e),
    }
}

pub fn generate_proof(
    params: &Params<EqAffine>,
    pk: &ProvingKey<EqAffine>,
    circuit: &RegexCircuit<Fp>,
    pub_input1: &Vec<Fp>,
    pub_input2: &Vec<Fp>,
) -> Vec<u8> {
    println!("Generating proof...");
    let proof = {
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof(
            params,
            pk,
            &[circuit.clone()],
            &[&[pub_input1,pub_input2]],
            OsRng,
            &mut transcript,
        )
        .unwrap();
        transcript.finalize()
    };
    proof
}
// Verifies the proof 
pub fn verify(
    params: &Params<EqAffine>,
    vk: &VerifyingKey<EqAffine>,
    pub_input1: &Vec<Fp>,
    pub_input2: &Vec<Fp>,
    proof: Vec<u8>,
) -> Result<(), Error> {
    
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    let strategy = SingleVerifier::new(&params);
    verify_proof(
        params,
        &vk,
        strategy,
        &[&[pub_input1,pub_input2]],
        &mut transcript,
    )
}

fn main() {
    let regex1_decomposed: DecomposedRegexConfig =
                serde_json::from_reader(File::open("./examples/regex_example.json").unwrap())
                    .unwrap();
    
    regex1_decomposed
        .gen_regex_files(
            &Path::new("./examples/ex_allstr.txt").to_path_buf(),
            &[Path::new("./examples/ex_substr_id1.txt").to_path_buf()],
        )
        .unwrap();
    let text = "email  from: vital vitalik@gmail to: some some@outlook.com   etc.";
    let characters: Vec<u8> = text
        .chars()
        .map(|c| c as u8)
        .collect();

    let circuit = create_circuit(characters);

    // Generate instance
    let (expected_masked_chars, expected_masked_substr_ids) = gen_masked_instance(text);
    

    //Draw circuit layout
    draw_circuit(K as u32, &circuit);

    //MockProve
    run_mock_prover(
        K as u32,
        &circuit,
        &expected_masked_chars, 
        &expected_masked_substr_ids,
    );


    // Generate and verify proofs
    //let (masked_chars, masked_substr_ids) = gen_masked_instance(text);
    let params = generate_setup_params(K as u32);
    let empty_circuit = create_circuit(vec![]);
    
    // generate proving and verifying keys
    let (pk, vk) = generate_keys(&params, &empty_circuit);
    // Generate proof
    let proof = generate_proof(&params, &pk, &circuit, &expected_masked_chars,&expected_masked_substr_ids);
   
    // Verify proof
    let verify = verify(&params, &vk, &expected_masked_chars,&expected_masked_substr_ids, proof);
    println!("Proof verification result: {:?}", verify);
    
   
}



