//! Defines functions and structures for linking predicate proofs into a single "linkage proof"

use crate::{
    attrs::{Attrs, AttrsVar},
    com_forest::PreparedRoots,
    pred::PredicateChecker,
    proof_data_structures::{
        ForestProof, ForestVerifyingKey, PredProof, PredVerifyingKey, TreeProof, TreeVerifyingKey,
    },
    Com,
};

use ark_crypto_primitives::{
    commitment::{constraints::CommitmentGadget, CommitmentScheme},
    crh::{constraints::TwoToOneCRHGadget, TwoToOneCRH},
};
use ark_ec::PairingEngine;
use ark_ff::{ToConstraintField, Zero};
use ark_relations::r1cs::SynthesisError;
use ark_std::rand::{CryptoRng, Rng};
use linkg16::{groth16, LinkedProof};
use std::time::Instant;

#[derive(Clone)]
pub struct PredPublicInputs<E: PairingEngine>(Vec<E::G1Projective>);

impl<E: PairingEngine> Default for PredPublicInputs<E> {
    fn default() -> PredPublicInputs<E> {
        PredPublicInputs(Vec::default())
    }
}

impl<E: PairingEngine> PredPublicInputs<E> {
    pub fn prepare_pred_checker<P, A, AV, AC, ACG, H, HG>(
        &mut self,
        pred_verif_key: &PredVerifyingKey<E, A, AV, AC, ACG, H, HG>,
        checker: &P,
    ) where
        P: PredicateChecker<E::Fr, A, AV, AC, ACG>,
        A: Attrs<E::Fr, AC>,
        AV: AttrsVar<E::Fr, A, AC, ACG>,
        AC: CommitmentScheme,
        AC::Output: ToConstraintField<E::Fr>,
        ACG: CommitmentGadget<AC, E::Fr>,
        H: TwoToOneCRH,
        H::Output: ToConstraintField<E::Fr>,
        HG: TwoToOneCRHGadget<H, E::Fr>,
    {
        // First set the common inputs to zero. This is filled in by the GS linking proof
        let attr_com_len = Com::<AC>::default().to_field_elements().unwrap().len();
        let root_len = H::Output::default().to_field_elements().unwrap().len();
        let common_inputs = vec![E::Fr::zero(); attr_com_len + root_len];

        // Now add the public inputs of this predicate
        let mut pred_public_input = common_inputs;
        pred_public_input.extend(checker.public_inputs());

        // Prepare the inputs and add them to the list of predicate inputs
        let prepared = groth16::prepare_inputs(&pred_verif_key.vk, &pred_public_input).unwrap();
        self.0.push(prepared);
    }
}

pub struct LinkVerifyingKey<E, A, AV, AC, ACG, H, HG>
where
    E: PairingEngine,
    A: Attrs<E::Fr, AC>,
    AV: AttrsVar<E::Fr, A, AC, ACG>,
    AC: CommitmentScheme,
    AC::Output: ToConstraintField<E::Fr>,
    ACG: CommitmentGadget<AC, E::Fr>,
    H: TwoToOneCRH,
    H::Output: ToConstraintField<E::Fr>,
    HG: TwoToOneCRHGadget<H, E::Fr>,
{
    pub pred_inputs: PredPublicInputs<E>,
    pub prepared_roots: PreparedRoots<E>,
    pub forest_verif_key: ForestVerifyingKey<E, A, AC, ACG, H, HG>,
    pub tree_verif_key: TreeVerifyingKey<E, A, AC, ACG, H, HG>,
    pub pred_verif_keys: Vec<PredVerifyingKey<E, A, AV, AC, ACG, H, HG>>,
}

impl<E, A, AV, AC, ACG, H, HG> Clone for LinkVerifyingKey<E, A, AV, AC, ACG, H, HG>
where
    E: PairingEngine,
    A: Attrs<E::Fr, AC>,
    AV: AttrsVar<E::Fr, A, AC, ACG>,
    AC: CommitmentScheme,
    AC::Output: ToConstraintField<E::Fr>,
    ACG: CommitmentGadget<AC, E::Fr>,
    H: TwoToOneCRH,
    H::Output: ToConstraintField<E::Fr>,
    HG: TwoToOneCRHGadget<H, E::Fr>,
{
    fn clone(&self) -> Self {
        Self {
            pred_inputs: self.pred_inputs.clone(),
            prepared_roots: self.prepared_roots,
            forest_verif_key: self.forest_verif_key.clone(),
            tree_verif_key: self.tree_verif_key.clone(),
            pred_verif_keys: self.pred_verif_keys.clone(),
        }
    }
}

pub struct LinkProofCtx<E, A, AV, AC, ACG, H, HG>
where
    E: PairingEngine,
    A: Attrs<E::Fr, AC>,
    AV: AttrsVar<E::Fr, A, AC, ACG>,
    AC: CommitmentScheme,
    AC::Output: ToConstraintField<E::Fr>,
    ACG: CommitmentGadget<AC, E::Fr>,
    H: TwoToOneCRH,
    H::Output: ToConstraintField<E::Fr>,
    HG: TwoToOneCRHGadget<H, E::Fr>,
{
    pub attrs_com: Com<AC>,
    pub merkle_root: H::Output,
    pub forest_proof: ForestProof<E, A, AC, ACG, H, HG>,
    pub tree_proof: TreeProof<E, A, AC, ACG, H, HG>,
    pub pred_proofs: Vec<PredProof<E, A, AV, AC, ACG, H, HG>>,
    pub vk: LinkVerifyingKey<E, A, AV, AC, ACG, H, HG>,
}

pub fn link_proofs<R, E, A, AV, AC, ACG, H, HG>(
    rng: &mut R,
    ctx: &LinkProofCtx<E, A, AV, AC, ACG, H, HG>,
) -> LinkedProof<E>
where
    R: Rng + CryptoRng,
    E: PairingEngine,
    A: Attrs<E::Fr, AC>,
    AV: AttrsVar<E::Fr, A, AC, ACG>,
    AC: CommitmentScheme,
    AC::Output: ToConstraintField<E::Fr>,
    ACG: CommitmentGadget<AC, E::Fr>,
    H: TwoToOneCRH,
    H::Output: ToConstraintField<E::Fr>,
    HG: TwoToOneCRHGadget<H, E::Fr>,
{
    // Get the number of field elements that the two proofs have in common. This is just
    // |attrs_com| + |root|
    let common_inputs = {
        let attr_com_input = ctx.attrs_com.to_field_elements().unwrap();
        let root_input = ctx.merkle_root.to_field_elements().unwrap();
        &[attr_com_input, root_input].concat()
    };

    // Collect (vk, proof) for all our predicates
    let pred_pairs: Vec<(&groth16::VerifyingKey<E>, &groth16::Proof<E>)> = ctx
        .vk
        .pred_verif_keys
        .iter()
        .zip(ctx.pred_proofs.iter())
        .map(|(vk, proof)| (&vk.vk, &proof.proof))
        .collect();

    // Collect (proof, vk) for the tree and forest
    let mut all_pairs = pred_pairs;
    all_pairs.push((&ctx.vk.tree_verif_key.vk, &ctx.tree_proof.proof));
    all_pairs.push((&ctx.vk.forest_verif_key.vk, &ctx.forest_proof.proof));

    linkg16::link(rng, &all_pairs, common_inputs)
}

pub fn verif_link_proof<E, A, AV, AC, ACG, H, HG>(
    proof: &LinkedProof<E>,
    vk: &LinkVerifyingKey<E, A, AV, AC, ACG, H, HG>,
) -> Result<bool, SynthesisError>
where
    E: PairingEngine,
    A: Attrs<E::Fr, AC>,
    AV: AttrsVar<E::Fr, A, AC, ACG>,
    AC: CommitmentScheme,
    AC::Output: ToConstraintField<E::Fr>,
    ACG: CommitmentGadget<AC, E::Fr>,
    H: TwoToOneCRH,
    H::Output: ToConstraintField<E::Fr>,
    HG: TwoToOneCRHGadget<H, E::Fr>,
{
    // The tree proof's public inputs are just the attrs com and root, i.e., all inputs are hidden
    let tree_prepared_inputs = groth16::prepare_inputs(&vk.tree_verif_key.vk, &[]).unwrap();

    // Collect (vk, prepared_inputs) for all our predicates
    let pred_tuples = vk
        .pred_verif_keys
        .iter()
        .zip(vk.pred_inputs.0.iter())
        .map(|(vk, input)| (&vk.vk, input))
        .collect();

    // Collect (vk, prepared_inputs) for the tree and forest
    let mut all_tuples: Vec<(&groth16::VerifyingKey<E>, &E::G1Projective)> = pred_tuples;
    all_tuples.push((&vk.tree_verif_key.vk, &tree_prepared_inputs));
    all_tuples.push((&vk.forest_verif_key.vk, &vk.prepared_roots.0));

    linkg16::verify_link(proof, &all_tuples)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        attrs::Attrs,
        com_forest::{gen_forest_memb_crs, test::random_tree, ComForest},
        com_tree::{gen_tree_memb_crs, verify_tree_memb, ComTree},
        pred::{gen_pred_crs, prove_pred, verify_pred},
        test_util::{
            AgeChecker, NameAndBirthYear, TestComSchemePedersen, TestComSchemePedersenG, TestTreeH,
            TestTreeHG, MERKLE_CRH_PARAM,
        },
    };

    use ark_bls12_381::{Bls12_381 as E, Fr};

    /// Tests a predicate that returns true iff the given `NameAndBirthYear` is at least 21
    #[test]
    fn evaluate_memb() {
        let mut rng: rand::prelude::StdRng = ark_std::test_rng();
        let mut compile_time_vec: Vec<u128> = vec![];
        let mut prove_time_vec: Vec<u128> = vec![];
        let mut verify_time_vec: Vec<u128> = vec![];
        let mut tree_height_vec: Vec<u32> = vec![];
        for i in (10..=32).step_by(2) {
            let tree_height = i;
            tree_height_vec.push(i);
            let mut start_time = Instant::now();
            // Generate the predicate circuit's CRS
            let tree_proving_key = gen_tree_memb_crs::<
                _,
                E,
                NameAndBirthYear,
                TestComSchemePedersen,
                TestComSchemePedersenG,
                TestTreeH,
                TestTreeHG,
            >(&mut rng, MERKLE_CRH_PARAM.clone(), tree_height)
            .unwrap();
            let mut elapsed_time = start_time.elapsed();

            println!("height: [{:?}] Compile: {:?}", tree_height, elapsed_time);
            compile_time_vec.push(elapsed_time.as_millis());

            // Make a attribute to put in the tree
            let person = NameAndBirthYear::new(&mut rng, b"Andrew", 1992);
            let person_com = Attrs::<_, TestComSchemePedersen>::commit(&person);

            // Make a tree and "issue", i.e., put the person commitment in the tree at index 17
            let leaf_idx = 17;
            let mut tree = ComTree::empty(MERKLE_CRH_PARAM.clone(), tree_height);
            let auth_path = tree.insert(leaf_idx, &person_com);

            // The person can now prove membership in the tree. Calculate the root and prove wrt that
            // root.
            let merkle_root = tree.root();

            start_time = Instant::now();
            let tree_proof = auth_path
                .prove_membership(&mut rng, &tree_proving_key, &*MERKLE_CRH_PARAM, person_com)
                .unwrap();

            elapsed_time = start_time.elapsed();
            println!("height: [{:?}] Prove: {:?}", tree_height, elapsed_time);
            prove_time_vec.push(elapsed_time.as_millis());


            let tree_verif_key = tree_proving_key.prepare_verifying_key();

            start_time = Instant::now();
            assert!(
                verify_tree_memb(&tree_verif_key, &tree_proof, &person_com, &merkle_root).unwrap()
            );

            elapsed_time = start_time.elapsed();
            println!("height: [{:?}] Verify: {:?}", tree_height, elapsed_time);
            verify_time_vec.push(elapsed_time.as_millis());
        }
        println!(
            "[{}]",
            tree_height_vec
                .iter()
                .map(|x| format!("{:.4}", x))
                .collect::<Vec<_>>()
                .join(", ")
        );
        println!(
            "[{}]",
            compile_time_vec
                .iter()
                .map(|x| format!("{:.4}", x))
                .collect::<Vec<_>>()
                .join(", ")
        );
        println!(
            "[{}]",
            prove_time_vec
                .iter()
                .map(|x| format!("{:.4}", x))
                .collect::<Vec<_>>()
                .join(", ")
        );
        println!(
            "[{}]",
            verify_time_vec
                .iter()
                .map(|x| format!("{:.4}", x))
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
}
