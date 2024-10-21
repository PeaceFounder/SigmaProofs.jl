using Test
using CryptoGroups
import SigmaProofs.SecretSharing: evaluate_poly, lagrange_coef, sharding_setup, verify, merge_exponentiations, merge_decryptions
import SigmaProofs.Verificatum: ProtocolSpec
import SigmaProofs.LogProofs: exponentiate, Exponentiation, ChaumPedersenProof
import SigmaProofs.ElGamal: Enc, a


G = @ECGroup{P_192}
g = G()

verifier = ProtocolSpec(; g)

N = 5 # participants
M = 3 # coefficients also the threshold

nodes = rand(2:order(G) - 1, N) 
coeff = rand(2:order(G) - 1, M)

sk = first(coeff)
pk = g^sk

d_vec = evaluate_poly(nodes, coeff, order(G))

elements = [g^2, g^3, g^5, g^8]
partials = [elements .^ di for di in d_vec]

# Evaluation at minimum threshold
l_vec = lagrange_coef(nodes[1:M], order(G)) 
@test mod(sum(d_vec[1:M] .* l_vec), order(G)) == sk
@test mapreduce(.^, .*, partials[1:M], l_vec) == elements .^ sk

# Evaluation with all decryptions
l_vec = lagrange_coef(nodes, order(G)) 
@test mod(sum(d_vec .* l_vec), order(G)) == sk
@test mapreduce(.^, .*, partials, l_vec) == elements .^ sk

# Sharding setup
setup = sharding_setup(g, nodes, coeff, verifier; d_vec)
@test verify(setup)

# The secrets are polynomial evaluations. The setup is published on the bulletin board; 
# every participant receives (ni, di) and tests that. As confirmation, the node announces 
# proof of knowledge for di on the bulletin board and signs that with the node’s identity 
# public key to establish a contract for participation in the threshold exponentiation ceremony.

elements = [g^2, g^3, g^5]

exponentiations = Exponentiation{G}[]
proofs = ChaumPedersenProof{G}[]

for (ni, di) in enumerate(d_vec)

    @test setup.proposition.public_keys[ni] == g^di

    simulator = exponentiate(g, elements, di, verifier) 
    @test verify(simulator)

    @test simulator.proposition.y == elements .^ di

    push!(exponentiations, simulator.proposition)
    push!(proofs, simulator.proof)
end

full_exponentiation = merge_exponentiations(setup, elements, exponentiations, proofs)
@test verify(full_exponentiation)

@test full_exponentiation.proposition.y == elements .^ sk

# A typical threshold decryption ceremony

m = [g^2, g^7, g^9] .|> tuple 
enc = Enc(pk, g)
ciphertexts = enc.(m, [5, 6, 9]) 

a_vec = Iterators.flatten(a(i) for i in ciphertexts) |> collect # need to define

exponentiations = Exponentiation{G}[]
proofs = ChaumPedersenProof{G}[]

for (ni, di) in enumerate(d_vec)

    simulator = exponentiate(g, a_vec, di, verifier) 

    @test verify(simulator)

    push!(exponentiations, simulator.proposition)
    push!(proofs, simulator.proof)

end

full_decryption = merge_decryptions(setup, ciphertexts, exponentiations, proofs)
@test verify(full_decryption)

@test full_decryption.proposition.plaintexts == m
