module Verificatum

using CryptoPRG: HashSpec, bitlength
using CryptoPRG.Verificatum: ROPRG, RO, PRG
using CryptoGroups: Group, PGroup, ECGroup, order, name, octet
using ..SigmaProofs: Verifier
using ..LogProofs: LogEquality, LogKnowledge
using ..CommitmentShuffle: Shuffle
using ..RangeProofs: ElGamalEnc, ElGamalBitRange, BitCommit
using ..Serializer: Serializer, Path
using ..Parser

import ..SigmaProofs: challenge, generator_basis

# This module represents Verifiactum verifier which implements verifier and associated generator basis
# functions. The Verificatum specification is only concrete with respect to ShuffleProofs, hence, implementation of verifier here is just an prelimenary imitation and would likelly be reviewed in the future.

include("GeneratorBasis.jl") # exports only a single function

using Base: @kwdef

@kwdef struct ProtocolSpec{G<:Group} <: Verifier
    g::G
    nr::Int32 = Int32(100)
    nv::Int32 = Int32(256)
    ne::Int32 = Int32(256)
    prghash::HashSpec = HashSpec("sha256")
    rohash::HashSpec = HashSpec("sha256")
    version::String = "3.0.4"
    sid::String = "SessionID"
    auxsid::String = "default"
end

Base.:(==)(x::ProtocolSpec{G}, y::ProtocolSpec{G}) where G <: Group = x.g == y.g && x.nr == y.nr && x.nv == y.nv && x.ne == y.ne && x.prghash == y.prghash && x.rohash == y.rohash && x.version == y.version && x.sid == y.sid && x.auxsid == y.auxsid

function marshal_s_Gq(g::PGroup)

    M = bitlength(order(g))

    tree = marshal(g)
    str = "ModPGroup(safe-prime modulus=2*order+1. order bit-length = $M)::" * string(tree)
    
    return Leaf(str)
end


function marshal_s_Gq(g::ECGroup)
    
    curve_name = Parser.normalize_ecgroup_name(name(g))
    tree = marshal(g)

    str = "com.verificatum.arithm.ECqPGroup($curve_name)::" * string(tree)

    return Leaf(str)
end

function map_hash_name(x::AbstractString)
    if x == "SHA-256"
        return "sha256"
    elseif x == "SHA-384"
        return "sha384"
    elseif x == "SHA-512"
        return "sha512"
    else
        error("No corepsonding mapping for $x implemented")
    end
end

function map_hash_name_back(x::AbstractString)
    if x == "sha256"
        return "SHA-256"
    elseif x == "sha384"
        return "SHA-384"
    elseif x == "sha512"
        return "SHA-512"
    else
        error("No corepsonding mapping for $x implemented")
    end
end 

map_hash_name_back(x::HashSpec) = map_hash_name_back(x.spec)


function ro_prefix(spec::ProtocolSpec)

    (; version, sid, auxsid, rohash, prghash, g, nr, nv, ne) = spec

    s_PRG = map_hash_name_back(prghash)
    s_H = map_hash_name_back(rohash)
    
    s_Gq = marshal_s_Gq(g)

    data = (version, sid * "." * auxsid, nr, nv, ne, s_PRG, s_Gq, s_H)

    tree = Tree(data)
    binary = encode(tree)

    ρ = rohash(binary)

    return ρ
end


function challenge(verifier::ProtocolSpec{G}, proposition::LogEquality{G}, commitment::Vector{G}) where G <: Group

    (; rohash, nv) = verifier

    ρ = ro_prefix(verifier)

    tree = Tree((proposition.g, commitment)) # Need to have BinaryParser within this package

    ro = RO(rohash, nv)
    𝓿 = Parser.interpret(BigInt, ro([ρ..., encode(tree)...]))

    return 𝓿
end


function challenge(verifier::ProtocolSpec{G}, proposition::LogKnowledge{G}, commitment::G; suffix = nothing) where G <: Group
    # the encoding is deserializable as `octet` returns fixed length output that depends on unerlying group
    # nevertheless it is recommended to use a proper canoncial encoding for this purpose which we shall skip

    (; g, y) = proposition
    
    ρ = ro_prefix(verifier)

    if !isnothing(suffix)
        suffix_tree = Parser.Tree(suffix)
        suffix_bytes = Parser.encode(suffix_tree)
    else
        suffix_bytes = UInt8[]
    end

    prg = PRG(verifier.prghash, [ρ..., octet(g)..., octet(y)..., octet(commitment)..., suffix_bytes...])
    return rand(prg, 2:order(G) - 1)
end

function challenge(verifier::ProtocolSpec{G}, proposition::Shuffle{G}, A::G) where G <: Group

    (; h, 𝐂, rows) = proposition
    𝐮 = (i.u for i in rows) |> collect

    ρ = ro_prefix(verifier)

    tree = Tree((h, 𝐮, 𝐂, A))
    prg = PRG(verifier.prghash, [ρ..., encode(tree)...])

    return rand(prg, 2:order(G) - 1, length(𝐂))
end

function challenge(verifier::ProtocolSpec{G}, proposition::ElGamalBitRange{G}, a₁::G, b₁::G, a₂::G, b₂::G) where G <: Group
    
    (; g, h, 𝐺, x, y) = proposition
    
    ρ = ro_prefix(verifier)

    tree = Tree((g, h, 𝐺, x, y, a₁, b₁, a₂, b₂))
    
    prg = PRG(verifier.prghash, [ρ..., encode(tree)...])

    return rand(prg, 2:order(G) - 1)
end

function challenge(verifier::ProtocolSpec{G}, proposition::BitCommit{G}, b₁::G, b₂::G) where G <: Group
    
    (; g, h, y) = proposition
    
    ρ = ro_prefix(verifier)

    tree = Tree((g, h, y, b₁, b₂))
    
    prg = PRG(verifier.prghash, [ρ..., encode(tree)...])

    return rand(prg, 2:order(G) - 1)
end

function challenge(verifier::ProtocolSpec{G}, proposition::ElGamalEnc{G}, t₁::G, t₂::G) where G <: Group

    (; g, pk, h, a, b) = proposition

    ρ = ro_prefix(verifier)

    tree = Tree((g, pk, h, a, b, t₁, t₂))

    prg = PRG(verifier.prghash, [ρ..., encode(tree)...])

    return rand(prg, 2:order(G) - 1)
end

leaf(x::String) = Parser.encode(Parser.Leaf(x))

function gen_verificatum_basis(::Type{G}, prghash::HashSpec, rohash::HashSpec, N::Integer; nr::Integer = 0, ρ = UInt8[], d = [ρ..., leaf("generators")...], suffix = UInt8[]) where G <: Group

    roprg = ROPRG(d, rohash, prghash)
    prg = roprg(suffix)

    return GeneratorBasis.generator_basis(prg, G, N; nr)
end


function generator_basis(verifier::ProtocolSpec{G}, ::Type{G}, N::Integer; ρ = ro_prefix(verifier), suffix = UInt8[]) where G <: Group
    (; g, nr, rohash, prghash) = verifier
    return gen_verificatum_basis(G, prghash, rohash, N; nr, ρ, suffix)
end


function fill_xml_template(template_path::String, replacements)
    # Read the template content
    template_content = read(template_path, String)

    # Replace placeholders with actual values
    for (placeholder, value) in replacements
        # An alternative would be replacing the XML tags themselves, however, that in general does not work
        # when XML is hierarchical and can have repeated tags.
        template_content = replace(template_content, "{{$placeholder}}" => value)
    end

    return template_content
end

function fill_protinfo_template(spec::ProtocolSpec; name="ShuffleProofs", descr="")

    (; g, nr, nv, ne, prghash, rohash, version, sid) = spec

    pgroup = String(marshal_s_Gq(g).x) # could be improved

    prg_hash = map_hash_name_back(prghash)
    ro_hash = map_hash_name_back(rohash)

    return fill_xml_template(joinpath(@__DIR__, "assets", "protInfo.xml"), [
        "VERSION" => version,
        "SID" => sid,
        "NAME" => name,
        "DESCR" => descr,
        "STATDIST" => nr,
        "PGROUP" => pgroup,
        "VBITLENRO" => nv,
        "EBITLENRO" => ne,
        "PRG" => prg_hash,
        "ROHASH" => ro_hash
    ])
end

function Serializer.save(spec::ProtocolSpec, path::Path; name="undefined")

    info = fill_protinfo_template(spec; name)
    write(path, info)
    
    return
end



function Serializer.load(::Type{T}, path::Path; auxsid = "default") where T <: ProtocolSpec

    _extract_group(::Type{ProtocolSpec{G}}) where G <: Group = G
    _extract_group(::Type{ProtocolSpec}) = nothing

    G = _extract_group(T)
    
    xml = read(path) |> String
    
    rohash = HashSpec(match(r"<rohash>(.*?)</rohash>", xml)[1] |> map_hash_name)
    prghash = HashSpec(match(r"<prg>(.*?)</prg>", xml)[1] |> map_hash_name)
    s_Gq = match(r"<pgroup>(.*?)</pgroup>", xml)[1]

    nr = parse(Int32, match(r"<statdist>(.*?)</statdist>", xml)[1])
    nv = parse(Int32, match(r"<vbitlenro>(.*?)</vbitlenro>", xml)[1])
    ne = parse(Int32, match(r"<ebitlenro>(.*?)</ebitlenro>", xml)[1])

    g = unmarshal(decode(split(s_Gq, "::")[2]))
    
    if !isnothing(G)
        g = convert(G, g)
    end

    version = match(r"<version>(.*?)</version>", xml)[1] |> String
    sid = match(r"<sid>(.*?)</sid>", xml)[1] |> String

    return ProtocolSpec(; g, nr, nv, ne, prghash, rohash, version, sid, auxsid)
end

Serializer.treespec(::Type{<:ProtocolSpec}) = "protInfo.xml"

end
