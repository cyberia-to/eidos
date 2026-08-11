---
tags: eidos, spec
crystal-type: spec
crystal-domain: eidos
status: draft
---
# certificate

a proof certificate is the output of a completed eidos proof. it attests that a specific kernel checked a specific proof term and accepted it. the certificate is a [[zheng]] proof of that kernel execution. it enters the [[cybergraph]] as a [[cyberlink]] — globally memoized, zero-cost to re-verify.

## what a certificate attests

a certificate for theorem `P` with proof `π` is evidence for:

```
check_kernel(Σ, [], π, P) = Ok
```

this is a nox execution. [[zheng]] certifies the execution trace, producing a proof that anyone can verify with the zheng verifier — a short nox program running in ~825 constraints.

## proof artifact

a proof artifact is the tuple:

```
ProofArtifact = {
  claim   : NounId,    -- hemera hash of the claim noun: CLAIM(P)
  proof   : NounId,    -- hemera hash of the proof noun: π
  kernel  : NounId,    -- hemera hash of the kernel formula noun
  stark   : Bytes,     -- zheng certificate bytes
  env_ref : NounId,    -- hemera hash of the global environment Σ used
}
```

all NounIds are [[hemera]] hashes (4 × Goldilocks field elements = 32 bytes).

### claim noun

the claim encodes the theorem being proved:

```
CLAIM(P) = cons(atom(0xC0), P)   -- tag 0xC0 marks a claim; payload is the type term
```

the tag separates claims from arbitrary terms in the cybergraph.

### proof noun

the proof term `π` is a kernel term (see [[terms]]) of type `P`. its NounId is `hemera(encode(π))`.

### kernel noun

the kernel formula is the nox program that implements the type checker (see [[kernel]]). its NounId is fixed at genesis — it is the identity of the trusted kernel. a different kernel NounId means a different TCB.

`KERNEL_ID` is a protocol constant announced at eidos genesis and stored in [[bbg]] namespace 0.

## axon computation

the axon is the content address of the proof event:

```
axon = hemera(KERNEL_ID || claim || proof)
```

this is a 32-byte hash. it uniquely identifies "kernel K checked proof π for claim P and accepted."

`||` is concatenation of the 32-byte hemera representations. the hemera sponge absorbs all three inputs sequentially with domain separator `0xA1` (proof-event domain).

## cyberlink encoding

the certificate enters the cybergraph as a cyberlink:

```
cyberlink: axon → OK
```

where `OK = atom(0x4F4B)` — the field element encoding of ASCII "OK". this is the canonical acceptance signal.

the cyberlink is signed by the prover's neuron key and staked with the prover's will, following standard [[cyberlink]] protocol. the cyberlink payload (stored as a particle in namespace 0) contains the full ProofArtifact encoded as a noun.

### particle encoding

the ProofArtifact encodes as a noun for cybergraph storage:

```
artifact_noun =
  cons(claim,
  cons(proof,
  cons(kernel,
  cons(env_ref,
  stark_atom))))

stark_atom = atom(hemera(stark_bytes))  -- the proof is content-addressed; full bytes stored off-chain
```

the full proof bytes are stored as a separate particle (content-addressed by their hemera hash). the artifact noun references the proof by hash, keeping the on-chain footprint small.

## zheng wrapping

the zheng proof certifies the nox execution of `check(Σ_noun, CTX_EMPTY, π_noun, P_noun)`.

### execution instance

the nox execution instance (public inputs) is:

```
instance = {
  object_id  : NounId,    -- input noun: cons(cons(Σ_ref, CTX_EMPTY), cons(π, P))
  formula_id : NounId,    -- kernel formula noun id
  result_id  : NounId,    -- expected result: atom(0x4F4B) = OK
  status     : 0x00,      -- 0x00 = success
}
```

the proof attests: "reducing object with formula produces result within budget."

### proof format

the certificate is a [[zheng]] Whirlaway proof:

```
ZhengProof = {
  sumcheck_transcript : [Round],   -- k rounds of sumcheck
  brakedown_opening   : Opening,   -- polynomial evaluation at challenge point
  claimed_evaluation  : F,         -- the evaluation claim
}

Round = {
  poly_coeffs : [F; 3],   -- round polynomial g_i(X) of degree ≤ 2
  challenge   : F,        -- Fiat-Shamir challenge r_i
}

Opening = {
  commitment : Hash,       -- Brakedown commitment to the trace polynomial
  path       : [Hash],     -- Merkle path for evaluation proof
  leaf_value : F,
}
```

all field elements are Goldilocks elements (8 bytes each). the proof is approximately 2–4 KB for typical kernel executions.

### verifier algorithm

`verify(instance, stark) → accept | reject`:

```
1. initialize Fiat-Shamir transcript with instance fields
2. for i = 1..k:
   absorb stark.sumcheck_transcript[i].poly_coeffs into transcript
   r_i = squeeze transcript
   check: g_i(0) + g_i(1) = claim_{i-1}   -- sumcheck consistency
   claim_i = g_i(r_i)
3. evaluate the constraint polynomial at r = (r_1, ..., r_k):
   C_eval = constraint_eval(instance, r)
4. check: C_eval = claim_k
5. verify Brakedown opening at r against committed trace
```

the verifier runs as a nox program of ~825 constraint rows. verifier cost is O(log² N) in the trace size N.

## memoization protocol

when a neuron wants to prove P and a cyberlink `axon → OK` already exists in the cybergraph:

```
memo_lookup(P, kernel_id) =
  axon = hemera(kernel_id || CLAIM(P) || _)  -- wildcard on proof
```

the cybergraph does not support wildcard queries directly. instead: query particles tagged with CLAIM(P) in namespace 0, check if any existing axon matches. if found: re-use the existing cyberlink. cost: one BBG lookup.

if the prover wants to verify the existing certificate: fetch the ProofArtifact particle, recover the proof, run `verify(instance, stark)`. this costs ~825 nox rows — constant time regardless of how complex the original proof was.

## certificate pipeline

the end-to-end flow from completed tactic proof to cyberlink:

```
1. tactic engine produces: π (proof term noun)
2. kernel verifies: check(Σ, [], π, P) = Ok
3. compute:
   claim   = hemera(CLAIM(P))
   proof   = hemera(encode(π))
   axon    = hemera(KERNEL_ID || claim || proof)
4. run zheng prover on the kernel execution trace → stark_bytes
5. build ProofArtifact noun
6. publish particle: hemera(artifact_noun) → artifact_noun content
7. publish stark particle: hemera(stark_bytes) → stark_bytes
8. sign cyberlink: axon → OK
9. broadcast cyberlink to the network
```

steps 4–9 are performed by the untrusted shell. step 2 is the only trusted step (kernel). a bug in steps 4–9 produces a verifiable certificate that the verifier rejects — it cannot produce a certificate the verifier accepts for a false theorem.

## global theorem database

every accepted certificate produces a cyberlink in the global cybergraph. the cybergraph is the universal theorem database for [[cyber]]:

- `hemera(KERNEL_ID || claim || proof) → OK` — the specific proof was accepted
- queries: given a claim noun, find all proofs of it
- inter-operability: any neuron (human, AI, sensor, program) can submit proofs and read certificates

the memoization invariant: if `axon → OK` exists in the cybergraph, then there exists a valid zheng proof attesting `check_kernel(π, P) = Ok`. re-proving the same theorem at the same kernel version costs zero network resources — the second prover reads the existing cyberlink.

## versioning

the kernel NounId is pinned. a new kernel version (new NounId) produces different axons — old certificates remain valid under the old kernel. migration paths:

- upward compatibility: the new kernel accepts a superset of proofs; old certificates remain valid if the old kernel is still trusted
- explicit re-proof: submit the same proof π to the new kernel, produce a new certificate under the new KERNEL_ID

the protocol records the KERNEL_ID in every artifact noun, so certificates are self-describing with respect to which kernel version accepted them.
