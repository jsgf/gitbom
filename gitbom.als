// Basic object id
abstract sig Oid {}

// Distinct artifact ids and bom doc ids
sig ArtifactOid, BomOid extends Oid {}

// Base of all artifacts
abstract sig Artifact {
	artoid: ArtifactOid
}

// Distinct leaf and derived artifacs
sig LeafArtifact, DerivedArtifact extends Artifact {}

// When a BomDoc references a derived artifact
// it also references its corresponding BomDoc
sig DerivedRef {
	bom: BomOid,
	artifact: ArtifactOid,
} {
	artifact in DerivedArtifact.artoid
}

// A document representing a build step
sig BomDoc {
	bomoid: BomOid,
	// Question: at least one input?
	inputs: some LeafArtifact + DerivedRef
}

// Constraints
fact {
	// Make sure things are attached (no free floating ids)
	no ArtifactOid - univ.artoid
	no BomOid - univ.bomoid
	no DerivedRef - univ.inputs
	// Oids are only used for one thing
	all oid: Oid | one (~artoid + ~bomoid)[oid]
	// Identities
	all disj a1, a2: Artifact | a1.artoid != a2.artoid
	all disj br1, br2: DerivedRef | br1.bom != br2.bom or br1.artifact != br2.artifact
	all disj b1, b2: BomDoc {
		// different bomdocs have distinct ids and inputs
		b1.bomoid != b2.bomoid
		b1.inputs != b2.inputs
	}
	// BomDocs can't reference themselves cyclically
	no iden & ^(inputs . bom . ~bomoid)
}


run {} for 10
