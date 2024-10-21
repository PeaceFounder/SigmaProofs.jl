module DecryptionProofs

using ..Serializer: Serializer, Path, load
using ..SigmaProofs.Parser: Parser, Tree
using ..SigmaProofs: Proposition, Verifier, Simulator
using ..ElGamal: ElGamalRow
using ..LogProofs: ChaumPedersenProof, LogEquality
using CryptoGroups: Group
using Base.Iterators: flatten
import ..SigmaProofs: prove, verify, proof_type

a(e::ElGamalRow{<:Group, N}) where N = ntuple(n -> e[n].a, N)
b(e::ElGamalRow{<:Group, N}) where N = ntuple(n -> e[n].b, N)

struct Decryption{G <: Group, N} <: Proposition
    g::G
    pk::G
    ciphertexts::Vector{ElGamalRow{G, N}}
    plaintexts::Vector{NTuple{N, G}}
end

proof_type(::Type{Decryption}) = ChaumPedersenProof
proof_type(::Type{<:Decryption{G}}) where G <: Group = ChaumPedersenProof{G}

Base.:(==)(x::T, y::T) where T <: Decryption = x.g == y.g && x.pk == y.pk && x.ciphertexts == y.ciphertexts && x.plaintexts == y.plaintexts

function Base.permute!(decr::Decryption, perm::AbstractVector{<:Integer})
    
    permute!(decr.ciphertexts, perm)
    permute!(decr.plaintexts, perm)

    return
end

verify(proposition::Decryption, secret::Integer) = decrypt(proposition.g, proposition.ciphertexts, secret) == proposition

axinv(proposition::Decryption) = (mi ./ b(ei) for (ei, mi) in zip(proposition.ciphertexts, proposition.plaintexts))
axinv(e::Vector{<:ElGamalRow}, secret::Integer) = (a(ei) .^ (-secret) for ei in e)

function decrypt(g::G, ciphertexts::Vector{<:ElGamalRow{G}}, secret::Integer; axinv = axinv(ciphertexts, secret)) where G <: Group

    plaintexts = [b(ci) .* axi for (ci, axi) in zip(ciphertexts, axinv)]
    pk = g^secret

    return Decryption(g, pk, ciphertexts, plaintexts)
end

function prove(proposition::Decryption{G}, verifier::Verifier, secret::Integer; axinv = axinv(proposition)) where G <: Group

    g_vec = [proposition.g, flatten(a(c) for c in proposition.ciphertexts)...]
    y_vec = [inv(proposition.pk), flatten(axinv)...]
    
    log_proposition = LogEquality(g_vec, y_vec)

    log_proof = prove(log_proposition, verifier, -secret)
    
    return log_proof
end

function decrypt(g::G, ciphertexts::Vector{<:ElGamalRow{G}}, secret::Integer, verifier::Verifier; axinv = axinv(ciphertexts, secret)) where G <: Group

    proposition = decrypt(g, ciphertexts, secret; axinv)
    proof = prove(proposition, verifier, secret; axinv)

    return Simulator(proposition, proof, verifier)
end


function verify(proposition::Decryption, proof::ChaumPedersenProof, verifier::Verifier)

    g_vec = [proposition.g, flatten(a(c) for c in proposition.ciphertexts)...]
    y_vec = [inv(proposition.pk), flatten(axinv(proposition))...]

    log_proposition = LogEquality(g_vec, y_vec)
    
    return verify(log_proposition, proof, verifier)
end


# An alternative way to construct a proof
# benefit is that ax can be computed more efficeintly this way and messages do not need to be inverted
# A bit complex though
struct DecryptionInv{G <: Group, N} <: Proposition
    g::G
    pk::G
    ciphertexts::Vector{ElGamalRow{G, N}}
    trackers::Vector{NTuple{N, G}}
end

proof_type(::Type{DecryptionInv}) = ChaumPedersenProof
proof_type(::Type{<:DecryptionInv{G}}) where G <: Group = ChaumPedersenProof{G}

Base.:(==)(x::T, y::T) where T <: DecryptionInv = x.g == y.g && x.pk == y.pk && x.ciphertexts == y.ciphertexts && x.trackers == y.trackers

function Base.permute!(decr::DecryptionInv, perm::AbstractVector{<:Integer})
    
    permute!(decr.ciphertexts, perm)
    permute!(decr.trackers, perm)

    return
end

ax(proposition::DecryptionInv) = (ti .* b(ei) for (ei, ti) in zip(proposition.ciphertexts, proposition.trackers))
ax(e::Vector{<:ElGamalRow}, secret::Integer) = (a(ei) .^ secret for ei in e)

function decryptinv(g::G, ciphertexts::Vector{<:ElGamalRow{G}}, secret::Integer; ax = ax(ciphertexts, secret)) where G <: Group

    trackers = [axi ./ b(ci) for (ci, axi) in zip(ciphertexts, ax)]
    pk = g^secret

    return DecryptionInv(g, pk, ciphertexts, trackers)
end

# The same actually
function prove(proposition::DecryptionInv{G}, verifier::Verifier, secret::Integer; ax = ax(proposition)) where G <: Group

    g_vec = [proposition.g, flatten(a(c) for c in proposition.ciphertexts)...]
    y_vec = [proposition.pk, flatten(ax)...]
    
    log_proposition = LogEquality(g_vec, y_vec)

    log_proof = prove(log_proposition, verifier, secret)
    
    return log_proof
end


function decryptinv(g::G, ciphertexts::Vector{<:ElGamalRow{G}}, secret::Integer, verifier::Verifier; ax = ax(ciphertexts, secret)) where G <: Group

    proposition = decryptinv(g, ciphertexts, secret; ax)

    proof = prove(proposition, verifier, secret; ax)

    return Simulator(proposition, proof, verifier)
end

verify(proposition::DecryptionInv, secret::Integer) = decryptinv(proposition.g, proposition.ciphertexts, secret) == proposition

function verify(proposition::DecryptionInv, proof::ChaumPedersenProof, verifier::Verifier)

    g_vec = [proposition.g, flatten(a(c) for c in proposition.ciphertexts)...]
    y_vec = [proposition.pk, flatten(ax(proposition))...]

    log_proposition = LogEquality(g_vec, y_vec)
    
    return verify(log_proposition, proof, verifier)
end


function Serializer.save(proposition::Decryption, dir::Path) 
    
    (; g, pk, ciphertexts, plaintexts) = proposition

    pbkey_tree = Parser.marshal_publickey(pk, g)
    write(joinpath(dir, "publicKey.bt"), pbkey_tree)

    write(joinpath(dir, "Ciphertexts.bt"), Tree(ciphertexts))
    write(joinpath(dir, "Decryption.bt"), Tree(plaintexts)) # Decryption could be renamed to Plaintexts

    return
end

Serializer.save(proof::ChaumPedersenProof, ::Type{<:Decryption}, path::Path) = Serializer.save(proof, path; prefix="Decryption")

function Serializer.load(::Type{Decryption}, basedir::Path)
    
    publickey_tree = Parser.decode(read(joinpath(basedir, "publicKey.bt")))
    pk, g = Parser.unmarshal_publickey(publickey_tree; relative=true)

    G = typeof(g)

    ciphertexts_tree = Parser.decode(read(joinpath(basedir, "Ciphertexts.bt")))
    plaintexts_tree = Parser.decode(read(joinpath(basedir, "Decryption.bt")))

    N = 1 # ToDo: extract that from the tree

    ciphertexts = convert(Vector{ElGamalRow{G, N}}, ciphertexts_tree)
    plaintexts = convert(Vector{NTuple{N, G}}, plaintexts_tree)

    return Decryption(g, pk, ciphertexts, plaintexts)
end

Serializer.load(::Type{P}, ::Type{Decryption}, path::Path) where P <: ChaumPedersenProof = Serializer.load(P, path; prefix="Decryption")

# ToDO

function Serializer.save(proposition::DecryptionInv, dir::Path) 
    
    (; g, pk, ciphertexts, trackers) = proposition

    pbkey_tree = Parser.marshal_publickey(pk, g)
    write(joinpath(dir, "publicKey.bt"), pbkey_tree)

    write(joinpath(dir, "Ciphertexts.bt"), Tree(ciphertexts))
    write(joinpath(dir, "DecryptionInv.bt"), Tree(trackers)) # Decryption could be renamed to Plaintexts

    return
end

Serializer.save(proof::ChaumPedersenProof, ::Type{<:DecryptionInv}, path::Path) = Serializer.save(proof, path; prefix="DecryptionInv")

function Serializer.load(::Type{DecryptionInv}, basedir::Path)
    
    publickey_tree = Parser.decode(read(joinpath(basedir, "publicKey.bt")))
    pk, g = Parser.unmarshal_publickey(publickey_tree; relative=true)

    G = typeof(g)

    ciphertexts_tree = Parser.decode(read(joinpath(basedir, "Ciphertexts.bt")))
    plaintexts_tree = Parser.decode(read(joinpath(basedir, "DecryptionInv.bt")))

    N = 1 # ToDo: extract that from the tree

    ciphertexts = convert(Vector{ElGamalRow{G, N}}, ciphertexts_tree)
    plaintexts = convert(Vector{NTuple{N, G}}, plaintexts_tree)

    return DecryptionInv(g, pk, ciphertexts, plaintexts)
end

Serializer.load(::Type{P}, ::Type{DecryptionInv}, path::Path) where P <: ChaumPedersenProof = Serializer.load(P, path; prefix="DecryptionInv")


Serializer.treespec(::Type{<:Decryption}) = (
    "publicKey.bt",
    "Ciphertexts.bt",
    "Decryption.bt"
)

Serializer.treespec(::Type{<:ChaumPedersenProof}, ::Type{<:Decryption}) = (
    "DecryptionCommitment.bt",
    "DecryptionReply.bt"
)

Serializer.treespec(::Type{<:DecryptionInv}) = (
    "publicKey.bt",
    "Ciphertexts.bt",
    "DecryptionInv.bt"
)

Serializer.treespec(::Type{<:ChaumPedersenProof}, ::Type{<:DecryptionInv}) = (
    "DecryptionInvCommitment.bt",
    "DecryptionInvReply.bt"
)


end
