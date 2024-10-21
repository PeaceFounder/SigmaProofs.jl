module SecretSharing

using CryptoGroups
using CryptoGroups.Utils: @check
using ..SigmaProofs.LogProofs: ChaumPedersenProof, Exponentiation
using ..SigmaProofs: Proposition, Proof, Verifier, Simulator
using ..SigmaProofs.ElGamal: ElGamalRow, a, b, width
import ..SigmaProofs: proof_type, prove, verify
import ..SigmaProofs.DecryptionProofs: Decryption

# Feldman's Verifiable Secret Sharing (VSS) scheme is a cryptographic protocol that extends Shamir's Secret Sharing
# with a verification mechanism. It allows a dealer to distribute shares of a secret among participants in a way
# that enables the participants to verify the consistency of their shares without revealing the secret.

# The Feldman VSS scheme works as follows:

# 1) The dealer chooses a prime p and a generator g of the multiplicative group of integers modulo p.
# 2) The dealer selects a random polynomial f(x) = a0 + a1x + a2x^2 + ... + at-1x^(t-1) mod p, where a0 is the secret.
# 3) For each participant i, the dealer computes the share si = f(i) mod p.
# 4) The dealer publishes commitments to the coefficients: C0 = g^a0, C1 = g^a1, ..., Ct-1 = g^a(t-1) mod p.
# 5) Each participant i can verify their share by checking if g^si = C0 * C1^i * C2^(i^2) * ... * Ct-1^(i^(t-1)) mod p.

# Decryption and Share Combination:
# To reconstruct the secret, a minimum number of t participants (where t is the threshold) must combine their shares.
# The secret is reconstructed using Lagrange interpolation:
# 1) Given t shares (x1, y1), (x2, y2), ..., (xt, yt), compute the Lagrange coefficients:
#    li = Π(j≠i) (xj / (xj - xi)) mod p
# 2) The secret a0 is then reconstructed as:
#    a0 = Σ(yi * li) mod p
# This process allows reconstruction of the secret without revealing individual shares, maintaining the scheme's security.

# This implementation provides functions for generating shares, creating commitments, verifying shares,
# and reconstructing the secret using the Feldman VSS scheme. It includes utilities for polynomial evaluation
# and Lagrange interpolation, which are essential for both the sharing and reconstruction processes.

# References
# - https://en.wikipedia.org/wiki/Verifiable_secret_sharing
# - Feldman, P. (1987). A practical scheme for non-interactive verifiable secret sharing.
# In 28th Annual Symposium on Foundations of Computer Science (sfcs 1987) (pp. 427-438). IEEE.
# https://www.cs.umd.edu/~gasarch/TOPICS/secretsharing/feldmanVSS.pdf

function evaluate_poly(x::Integer, coeff::Vector{<:Integer}, modulus::Integer) 

    s = BigInt(0)

    for (ai, i) in zip(coeff, 0:length(coeff)-1)
        s = s + ai * x^i % modulus
    end

    return s
end
 
evaluate_poly(nodes::Vector{<:Integer}, coeff::Vector{<:Integer}, modulus::Integer) = [evaluate_poly(ni, coeff, modulus) for ni in nodes]

function lagrange_coef(i::Integer, x::Vector{<:Integer}, modulus::Integer)

    l = BigInt(1)

    for j in 1:length(x)

        j == i && continue

        l *= x[j] * invmod(x[j] - x[i], modulus) % modulus
        
    end

    return l
end

lagrange_coef(nodes::Vector{<:Integer}, modulus::Integer) = [lagrange_coef(i, nodes, modulus) for i in 1:length(nodes)]

struct ShardingSetup{G<:Group} <: Proposition
    g::G
    pk::G
    poly_order::Int
    nodes::Vector{<:Integer}
    public_keys::Vector{G} # g^d_i
end

struct ShardingConsistency{G<:Group} <: Proof
    coeff_commitments::Vector{G}
end

proof_type(::Type{<:ShardingSetup{G}}) where G <: Group = ShardingConsistency{G}

function prove(proposition::ShardingSetup, verifier::Verifier, coeff::Vector{<:Integer}) 

    (; g, pk, nodes, public_keys, poly_order) = proposition

    @check poly_order == length(coeff) - 1
    
    coeff_commitments = [g^ai for ai in coeff]

    return ShardingConsistency(coeff_commitments)
end


function verify(proposition::ShardingSetup{G}, proof::ShardingConsistency{G}, verifier::Verifier) where G <: Group

    (; g, pk, poly_order, nodes, public_keys) = proposition

    any(>(0), nodes) || return false
    any(<(order(G)), nodes) || return false
    length(unique(nodes)) == length(nodes) || return false
    
    first(proof.coeff_commitments) == pk || return false

    for (xi, pki) in zip(nodes, public_keys)
        prod(ci^(xi^i) for (ci, i) in zip(proof.coeff_commitments, 0:poly_order)) == pki || return false
    end

    return true
end


function sharding_setup(g::G, nodes::Vector{<:Integer}, coeff::Vector{<:Integer}, verifier::Verifier;
                        d_vec = evaluate_poly.(nodes, coeff, order(G))
                        ) where G <: Group
  
    @check any(<(order(G)), nodes) && any(>(0), nodes) "A node must be withing interval `0 < node < order(G)`" 
    @check length(unique(nodes)) == length(nodes) "Nodes must be unique"

    pk = g^first(coeff) # first coefficient is a constant factor

    poly_order = length(coeff) - 1
    
    public_keys = g .^ d_vec

    proposition = ShardingSetup(g, pk, poly_order, nodes, public_keys)
    
    proof = prove(proposition, verifier, coeff)

    return Simulator(proposition, proof, verifier)
end

struct ThresholdExponentiation{G <: Group} <: Proof
    setup::ShardingSetup{G}
    consistency::ShardingConsistency{G}
    node_indices::Vector{Int}
    partials::Vector{Vector{G}}
    proofs::Vector{ChaumPedersenProof{G}}
end

Base.isvalid(::Type{<:ThresholdExponentiation{G}}, proposition::Exponentiation{G}) where G <: Group = true

function isbinding(setup::ShardingSetup{G}, elements::Vector{G}, proposition::Exponentiation{G}) where G <: Group

    proposition.g == setup.g || return false
    proposition.pk in setup.public_keys || return false
    proposition.x == elements || return false
    
    return true
end 

function merge_exponentiations(setup::Simulator{ShardingSetup{G}}, elements::Vector{G}, exponentiations::Vector{Exponentiation{G}}, proofs::Vector{ChaumPedersenProof{G}})::Simulator where G <: Group

    (; public_keys, poly_order, g, pk, nodes) = setup.proposition

    node_indices = Int[]
    partials = Vector{G}[]    

    # We could skip the wrong proofs here
    for (prop, proof) in zip(exponentiations, proofs)

        isbinding(setup.proposition, elements, prop)
        
        n = findfirst(isequal(prop.pk), public_keys)
        n in node_indices && continue # the same decryption

        push!(node_indices, n)
        push!(partials, prop.y) # this adds a pointer to the list thus it is efficient

        length(node_indices) == poly_order + 1 && break # may be better, we may also skip this one
    end

    @check length(node_indices) == poly_order + 1 "Not enough valid shares for full exponentiation"

    l_vec = lagrange_coef(nodes[node_indices], order(G)) 
    full_exponentiation = mapreduce(.^, .*, partials, l_vec)
    proposition = Exponentiation(g, pk, elements, full_exponentiation)

    proof = ThresholdExponentiation(setup.proposition, setup.proof, node_indices, partials, proofs)

    return Simulator(proposition, proof, setup.verifier)
end

# Note that the proofs are verified in advance hence one should not verify this seperatelly
function verify(proposition::Exponentiation{G}, proof::ThresholdExponentiation{G}, verifier::Verifier) where G <: Group

    (; setup, node_indices, partials, proofs) = proof
    (; g, public_keys, nodes) = setup
    (; x) = proposition

    verify(proof.setup, proof.consistency, verifier) || return false

    l_vec = lagrange_coef(nodes[node_indices], order(G))
    full_exponentiation = mapreduce(.^, .*, partials, l_vec)
    full_exponentiation == proposition.y || return false

    for (i, partial, proofi) in zip(node_indices, proof.partials, proof.proofs)

        pk = public_keys[i]

        propositioni = Exponentiation(g, pk, x, partial)

        verify(propositioni, proofi, verifier) || return false
    end

    return true
end

Base.isvalid(::Type{<:ThresholdExponentiation{G}}, proposition::Decryption{G}) where G <: Group = true

group_into_tuples(arr, N) = [Tuple(arr[i:i+N-1]) for i in 1:N:length(arr)]

function merge_decryptions(setup::Simulator{ShardingSetup{G}}, ciphertexts::Vector{<:ElGamalRow{G}}, exponentiations::Vector{Exponentiation{G}}, proofs::Vector{ChaumPedersenProof{G}})::Simulator where G <: Group

    a_vec = Iterators.flatten(a(ei) for ei in ciphertexts) #|> collect 
    b_vec = Iterators.flatten(b(ei) for ei in ciphertexts) #|> collect 

    simulator = merge_exponentiations(setup, collect(a_vec), exponentiations, proofs)

    (; y, g, pk) = simulator.proposition
    
    m_vec = b_vec ./ y
    
    plaintexts = group_into_tuples(m_vec, width(ciphertexts))

    proposition = Decryption(g, pk, ciphertexts, plaintexts)

    return Simulator(proposition, simulator.proof, setup.verifier)
end

function verify(proposition::Decryption{G}, proof::ThresholdExponentiation{G}, verifier::Verifier) where G <: Group

    (; g, pk, ciphertexts, plaintexts) = proposition

    a_vec = Iterators.flatten(a(ei) for ei in ciphertexts)
    b_vec = Iterators.flatten(b(ei) for ei in ciphertexts)
    
    m_vec = Iterators.flatten(plaintexts)

    ax_vec = b_vec ./ m_vec

    return verify(Exponentiation(g, pk, collect(a_vec), ax_vec), proof, verifier)
end

end
