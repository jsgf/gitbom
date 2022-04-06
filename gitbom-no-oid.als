// Simplified gitbom spec with implicit Oids
//
// This spec is simplified because objects reference each other directly
// rather than being mediated via oids. This makes the metamodel and
// constructed instances a bit more intuitive to read.

// Base of all artifacts
abstract sig Artifact {}

// Distinct leaf and derived artifacs
sig LeafArtifact, DerivedArtifact extends Artifact {} {
	this in univ.(inputs + artifact) // only interested in referenced artifacts
}

// When a BomDoc references a derived artifact
// it also references its corresponding BomDoc
// Source: https://gitbom.dev/glossary/gitbom/#gitbom-document
sig DerivedRef {
	bom: BomDoc,
	artifact: DerivedArtifact,
} {
	this in univ.inputs // only ever referenced as an input
}

// A document representing a build step
// A "GitBOM document" in  https://gitbom.dev/glossary/gitbom/#gitbom-document
sig BomDoc {
	// Inputs ("children") of this document. We can reference leaf artifacts
	// inputs directly, but derived artifacts also reference their corresponding
	// gitbom document.
	// Question: at least one input?
	inputs: some LeafArtifact + DerivedRef
}

// Constraints
// (facts are treated as axioms)
fact {
	// Identities
	all disj dr1, dr2: DerivedRef | dr1.bom != dr2.bom or dr1.artifact != dr2.artifact
	all disj b1, b2: BomDoc | b1.inputs != b2.inputs

	// no cyclic dependencies
	no_diamond_derives
}

// We can't have a derived artifact which was derived from itself.
// That is, it doesn't make sense to have a bomdoc depend on a derived
// artifact and also depend on another bomdoc which itself depends on
// the same derived artifact.
pred no_diamond_derives[] {
	all b: BomDoc | no b.inputs.artifact & b.inputs.^(bom.inputs).artifact
}

// BomDocs can't reference themselves cyclically
// This is weaker than no_diamond_derives, so it should be always true
pred non_cyclic_bom[] {
	no iden & ^(inputs . bom)
}

check invariants {
	non_cyclic_bom
}

run {} 
