using Test

using CryptoGroups
using SigmaProofs.Verificatum.GeneratorBasis: generator_basis
using SigmaProofs: Verifier, verify
using SigmaProofs.Verificatum: ProtocolSpec
using SigmaProofs.ElGamal: Enc
using CryptoPRG.Verificatum: PRG
using CryptoPRG: HashSpec
using SigmaProofs.RangeProofs: bitenc, bitcommit, rangecommit, elgamalenc, rangeenc, ElGamalBitRange, BitCommit, ElGamalEnc, PlaintextEquivalence, resetenc
using SigmaProofs.LogProofs: LogEquality

G = @ECGroup{P_192}
g = G()

verifier = ProtocolSpec(; g)

sk = 234
pk = g^sk
enc = Enc(g, pk)

𝐺 = let
    hasher = HashSpec("sha256")
    seed = Vector{UInt8}("SEED")
    prg = PRG(hasher, seed)
    generator_basis(prg, G)
end

h = let
    hasher = HashSpec("sha256")
    seed = Vector{UInt8}("BLINDING GENERATOR")
    prg = PRG(hasher, seed)
    generator_basis(prg, G)
end

α = 42

simulator_true = bitenc(g, pk, true, verifier; 𝐺, α)
@test verify(simulator_true)

simulator_false = bitenc(g, pk, false, verifier; 𝐺, α)
@test verify(simulator_false)

@test verify(simulator_false.proposition, simulator_true.proof, verifier) == false
@test verify(simulator_true.proposition, simulator_false.proof, verifier) == false

# Now doing the bitcommit

simulator_true = bitcommit(g, h, true, verifier; α)
@test verify(simulator_true)

simulator_false = bitcommit(g, h, false, verifier; α)
@test verify(simulator_false)

@test verify(simulator_false.proposition, simulator_true.proof, verifier) == false
@test verify(simulator_true.proposition, simulator_false.proof, verifier) == false
# rangecommit

simulator = rangecommit(4, g, h, 13, verifier)
@test verify(simulator)

for i in 0:15
    local simulator = rangecommit(4, g, h, i, verifier)
    @test verify(simulator)
end

simulator = rangecommit(4, g, h, 16, verifier; α, skip_checks = true)
@test verify(simulator) == false

# arbitrary rangeproof

simulator = rangecommit(45:55, g, h, 44, verifier; skip_checks = true)
@test verify(simulator) == false

simulator = rangecommit(45:55, g, h, 45, verifier)
@test verify(simulator) == true

simulator = rangecommit(45:55, g, h, 55, verifier)
@test verify(simulator) == true

simulator = rangecommit(45:55, g, h, 56, verifier; skip_checks = true)
@test verify(simulator) == false

# Correct ElGamal encryption proof; Ensures that e = (a, b) = (g^α, pk^α * h^m)
# h must be independent from g for the proof to be binding

simulator = elgamalenc(g, pk, 𝐺, 3, verifier)
@test verify(simulator)

# Now combining things together

simulator = rangeenc(4, g, pk, 9, verifier; 𝐺)
@test verify(simulator)

# With arbitrary ranges
simulator = rangeenc(2:11, g, pk, 9, verifier; 𝐺)
@test verify(simulator)

# Resetting a blinding factor of the palintext. This can be useful in situations where blinding factors can't be directly forwarded, but decryptor want's to make a proofs about the plaintext.

m = g^4
(; a, b) = enc(m, 23)
α = 56 # proofs can be delivered that way

simulator = resetenc(g, pk, a, b, sk, α, verifier)
@test verify(simulator)
