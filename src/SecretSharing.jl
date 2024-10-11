module SecretSharing

# TODO: NEED TO DO TDD TO GET THE CODE IN WORKING STATE

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

function evaluate_poly(x::BigInt, poly::Vector{BigInt}, modulus::BigInt) 

    s = BigInt(0)

    for (ai, i) in zip(coeff, 0:length(coeff)-1)
        s = s + ai * x^i % modulus
    end

    return s
end

function lagrange_coef(i::Int, x::Vector{BigInt}, modulus::BigInt)

    l = BigInt(1)

    for j in 1:length(x)

        j == i && continue

        l *= x[j] * modinv(x[j] - x[i], modulus) % modulus
        
    end

    return l
end

lagrange_coefs(nodes::Vector{BigInt}, modulus::BigInt) = [lagrange_coef(i, nodes, modulus) for i in 1:length(nodes)]

# The blinding is completelly unnecessary here as the secret space is large. It could be an interesting addition for a situation
# where 
struct ShardingSetup{G<:Group} <: Proposition
    g::G
    pk::G
    poly_order::Int
    nodes::Vector{BigInt}
    public_keys::Vector{G} # g^d_i
end

struct ShardingConsistency{G<:Group} <: Proof
    coeff_commitments::Vector{G}
end

function prove(proposition::ShardingSetup{G<:Group}, verifier::Verifier, coeff::Vector{BigInt})

    (; g, pk, nodes, public_keys, poly_order) = proposition

    @check poly_order == length(coeff) - 1
    
    coeff_commitments = [g^ai for ai in coeff]

    return ShardingConsistency(coeff_commitments)
end


function verify(proposition::ShardingSetup{G}, proof::ShardingConsistency{G}, verifier::Verifier) where G <: Group

    (; g, h, pk, nodes, public_keys, poly_order) = proposition

    for (xi, pki) in zip(nodes, public_keys)
        prod(ci^(x^i) for (ci, i) in zip(proof.coeff_commitments, 0:poly_order)) == pki || return false
    end

    return true
end


function sharding_setup(g::G, nodes::Vector{BigInt}, coeff::Vector{BigInt}, verifier::Verifier) where G <: Group

    @check !any(iszero, nodes) "A node can't be zero" 
    @check !any(>(0), nodes) "A node must be positive" 
    @check length(unique(nodes)) == length(nodes) "Nodes must be unique"

    pk = g^first(coeff) # first coefficient is a constant factor

    poly_order = length(coeff) - 1

    d_vec = evaluate_poly.(nodes, coeff, order(G))
    
    public_keys = g .^ d_vec

    proposition = ShardingSetup(g, pk, poly_order, nodes, public_keys)
    
    proof = prove(proposition, verifier, coeff)

    return Simulator(proposition, proof, verifier)
end


### Threshold decryption 

struct PartialDecryption{G<:Group} <: Proposition
    g::G
    pk::G # The public key must be one in the list of public_keys of sharding_setup
    a::Vector{G}
    ad::Vector{G}
end

function prove(proposition::PartialDecrytion, verifier::Verifier, sk::BigInt)

    (; g, pk, a, ad) = proposition

    g_vec = [g, a...]
    y_vec = [pk, ad...]

    proof = prove(LogEquality(g_vec, y_vec), verifier, sk)

    return proof
end

function verify(proposition::PartialDecryption, proof::ChaumPedersenProof, verifier::Verifier)

    (; g, pk, a, ad) = proposition

    g_vec = [g, a...]
    y_vec = [pk, ad...]

    return verify(LogEquality(g_vec, y_vec), proof, verifier)
end


function partialdecrypt(g::G, a::Vector{G}, sk::BigInt, verifier::Verifier)

    pk = g^sk
    ad = a .^ sk

    proposition = PartialDecryption(g, ok, a, ad)
    proof = prove(proposition, verifier, sk)

    return Simulator(proposition, proof, verifier)
end

struct FullDecryption{G<:Group, N} <: Proposition
    setup::ShardingSetup{G}
    cyphertexts::Vector{ElGamalRow{G, N}}
    plaintexts::Vector{NTuple{N, G}}
end

struct FullDecryptionProof{G<:Group} <: Proof
    partial_decryptions::Vector{Vector{G}}
    decryption_proofs::Vector{ChaumPedersenProof{G}}
end


a(e::ElGamalRow{<:Group, N}) where N = ntuple(x -> x[N].a, 1:N)

group_into_tuples(arr, N) = [Tuple(arr[i:i+N-1]) for i in 1:N:length(arr)]

# merge
function combine(setup::ShardingSetup{G}, cyphertexts::Vector{ElGamalRow{G, N}}, decryptions::Vector{PartialDecryption{G}}, proofs::Vector{ChaumPedersenProof{G}}, verifier::Verifer)::Simulator where {G <: Group, N}

    #a_vec = [g, flatten(a(c) for c in cyphertexts)...]
    a_vec = [flatten(a(c) for c in cyphertexts)...]
    b_vec = [flatten(b(c) for c in cyphertexts)...]

    for dec in decryptions
        decryption.g == setup.g || return false
        decrytpion.pk in setup.public_keys || return false # 
        a_vec == dec.a || return false
    end

    nodes = BigInt[]
    partials = Vector{G}[]    

    # We could skip the wrong proofs here
    for (prop, proof) in zip(decryptions, proofs)
        verify(prop, proof, verifier) || continue

        n = findfirst(=(prop.pk), setup.public_keys)
        setup.nodes[n] in nodes && continue

        push!(setup.nodes[n], nodes)
        push!(partials, prop.ad) # this adds a pointer to the list thus it is efficient

        length(nodes) == setup.poly_order && break
    end

    @check length(nodes) == setup.poly_order "Not enough valid shares decrypted to reconstruct the proof"

    l_vec = lagrange_coefs(nodes, modulus)

    plaintext_vec = prod(Pi .^ li for (Pi, li) in zip(partials, l_vec)) .* b_vec

    plaintexts = group_into_tuples(plaintext_vec, N)

    proposition = FullDecryption(setup, cyphertexts, plaintexts)

    proof = FullDecryptionProof(decryptions, proofs)

    return Simulator(proposition, proof, verifier)
end


function verify(proposition::FullDecryption{G}, proof::FullDecryptionProof, verifier::Verifier)

    (; g, pk, cyphertexts, plaintexts) = proposition.setup

    # We could run the combine method

    a_vec = [g, flatten(a(c) for c in cyphertexts)...]
    
    propositions = [PartialDecryption(g, pk, a_vec, ad_vec) for ad_vec in proof.partial_decryptions]

    simulator = combine(proposition.setup, cyphertexts, propositions, proof.decryption_proofs, verifier)

    return simulator.proposition.plaintexts == plaintexts
end


end
