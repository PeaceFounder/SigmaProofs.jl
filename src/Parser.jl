module Parser

using ...ElGamal: ElGamalRow
using CryptoGroups.Curves: a, b, field, gx, gy
using CryptoGroups: PGroup, ECGroup, Group, value, concretize_type, spec, generator, name, ECPoint, modulus, order, octet
using CryptoPRG.Verificatum: HashSpec
import CryptoGroups.Fields: bitlength # TODO: import -> using
using CryptoGroups.Utils: int2octet, @check

import Base.convert
import Base.==

tobig(x) = parse(BigInt, bytes2hex(reverse(x)), base=16)
interpret(::Type{BigInt}, x::Vector{UInt8}) = tobig(reverse(x))

function interpret(::Type{T}, x::AbstractVector{UInt8}) where T <: Integer 
    L = bitlength(T) ÷ 8
    result = zero(T)
    for i in 1:min(length(x), L)
        result |= T(x[length(x)-i+1]) << (8(i-1)) # @inbounds
    end
    return result
end

function interpret(::Type{Vector{UInt8}}, x::BigInt) 

    @check x > 0
    
    hex = string(x, base=16)
    if mod(length(hex), 2) != 0
        hex = string("0", hex)
    end

    return hex2bytes(hex)
end

interpret(::Type{Vector{UInt8}}, x::Integer) = reverse(reinterpret(UInt8, [x])) # Number of bytes are useful for construction for bytes. 

function interpret(::Type{Vector{T}}, 𝐫::Vector{UInt8}, N::Int) where T <: Integer
    M = length(𝐫) ÷ N
    𝐮 = reshape(𝐫, (M, N))
    𝐭 = [interpret(T, 𝐮[:, i]) for i in 1:N]
    return 𝐭
end

const NODE = UInt8(0)
const LEAF = UInt8(1)

abstract type Tree end

Base.string(x::Tree) = bytes2hex(encode(x))

struct Leaf <: Tree
    x::Vector{UInt8} # Bytes
end

==(a::Leaf, b::Leaf) = a.x == b.x

struct Node <: Tree
    x::Vector{Tree} # Leaf or Node
end

Base.getindex(node::Node, index::Int) = node.x[index]
Base.length(node::Node) = length(node.x)

==(a::Node, b::Node) = a.x == b.x

Node() = Node([])

Base.push!(n::Node, y) = push!(n.x, y)

toint(x) = reinterpret(UInt32, x[4:-1:1])[1] ### TOREMOVE


# Add position tracking to avoid array slicing
mutable struct BinaryParser
    data::Vector{UInt8}
    pos::Int
end

function read_uint32!(parser::BinaryParser)
    val = interpret(UInt32, @view parser.data[parser.pos:parser.pos+3])
    parser.pos += 4
    return val
end

function read_bytes!(parser::BinaryParser, len::Integer)
    bytes = @view parser.data[parser.pos:parser.pos+len-1]
    parser.pos += len
    return bytes
end

function parseb!(parser::BinaryParser)
    marker = parser.data[parser.pos]
    parser.pos += 1
    
    if marker == LEAF
        L = read_uint32!(parser)
        bytes = read_bytes!(parser, L)
        return Leaf(bytes)
    elseif marker == NODE
        N = read_uint32!(parser)
        node = Node()
        sizehint!(node.x, N)  # Pre-allocate space for children
        for _ in 1:N
            child = parseb!(parser)
            push!(node, child)
        end
        return node
    else
        throw(ArgumentError("Invalid marker byte: $marker"))
    end
end

# Main entry point that maintains the same interface
function parseb(x::Vector{UInt8})
    parser = BinaryParser(x, 1)
    tree = parseb!(parser)
    remaining = if parser.pos <= length(x)
        @view x[parser.pos:end]
    else
        UInt8[]
    end
    return tree, remaining
end

decode(x::Vector{UInt8}) = parseb(x)[1]
decode(x::AbstractString) = decode(hex2bytes(replace(x, " "=>""))) # I could have optional arguments here as well

# Helper function to write UInt32 in correct byte order
function write_uint32!(io::IO, n::UInt32)
    # Write length in little-endian format
    bytes = reinterpret(UInt8, [n])
    # Reverse bytes to match expected format
    write(io, reverse(bytes))
end

function encode!(io::IO, leaf::Leaf)
    # Write type marker for leaf (01)
    write(io, UInt8(0x01))
    
    # Write length of data
    write_uint32!(io, UInt32(length(leaf.x)))
    
    # Write data directly
    write(io, leaf.x)
end

function encode!(io::IO, node::Node)
    # Write type marker for node (00)
    write(io, UInt8(0x00))
    
    # Write number of children
    write_uint32!(io, UInt32(length(node.x)))
    
    # Write all child nodes directly
    for child in node.x
        encode!(io, child)
    end
end

# Generic dispatch for Tree type
encode!(io::IO, tree::Tree) = encode!(io, tree)

# Optional convenience method that returns the encoded bytes
function encode(tree::Tree)
    io = IOBuffer()
    encode!(io, tree)
    take!(io)
end

convert(::Type{T}, x::Leaf) where T <: Integer = interpret(T, x.x)

function convert(::Type{String}, x::Leaf)
    return String(copy(x.x))
end

function convert(::Type{Vector{T}}, x::Node) where T #<: Integer 
    return T[convert(T, i) for i in x.x] 
end

function convert(cfact::Type{T}, x::Node) where T <: Tuple 
     return Tuple((convert(ci, xi) for (xi, ci) in zip(x.x, cfact.types)))
end

function Leaf(x::Signed)

    bytes = interpret(Vector{UInt8}, x) 

    # Adding a redundant byte to ensure that the number is positive. 
    if bytes[1] > 127
        return Leaf(UInt8[0, bytes...]) 
    else
        return Leaf(bytes)
    end
end

Leaf(x::Unsigned) = Leaf(interpret(Vector{UInt8}, x))

function interpret!(result::Vector{UInt8}, k::Integer, x::Integer)
    if x == 0
        fill!(result, 0x00)
        return 0
    end
    
    hex = string(x, base=16)
    bytes_needed = (length(hex) + 1) ÷ 2
    
    # Fill padding zeros if needed
    if k > bytes_needed
        fill!(view(result, 1:k-bytes_needed), 0x00)
    end
    
    # Ensure even length for hex string
    if mod(length(hex), 2) != 0
        hex = string("0", hex)
    end
    
    hex2bytes!(view(result, k-bytes_needed+1:k), hex) 
    
    return bytes_needed
end

function Leaf(x::Integer, k::Integer)
    result = Vector{UInt8}(undef, k)
    interpret!(result, k, x)
    return Leaf(result)
end

function Leaf(x::AbstractString)
    bytes = Vector{UInt8}(x)
    return Leaf(bytes)
end

Tree(x::Any) = Leaf(x) 
Tree(x::BigInt; L=bitlength(x)) = Leaf(x, div(L + 1, 8, RoundUp)) 
Tree(x::Node) = x
Tree(x::Leaf) = x
Tree(x::Tuple; L=nothing) = Node(x; L)


function Node(x::Tuple; L=nothing)
    node = Node()
    for i in x
        if isnothing(L)
            r = Tree(i)
        else
            r = Tree(i; L) # This would make issues when i would be a string or a group element
        end
        push!(node, r)
    end
    return node
end

############################ COMPOSITE TYPE PARSING ############################

function convert(::Type{Vector{G}}, x::Node; allow_one=false) where G <: Group 
    return G[convert(G, i; allow_one) for i in x.x] 
end


(h::HashSpec)(t::Tree) = h(convert(Vector{UInt8}, t))  ### need to relocate

# To be added to CryptoGroups
bitlength(::Type{G}) where G <: PGroup = bitlength(modulus(G)) 
bitlength(x::PGroup) = bitlength(modulus(x)) 

bitlength(::Type{ECGroup{P}}) where P <: ECPoint = bitlength(modulus(field(P)))
bitlength(g::G) where G <: ECGroup = bitlength(G)

Tree(x::PGroup; L = bitlength(x)) = Leaf(value(x), div(L + 1, 8, RoundUp))

# Probably I will need to replace 
convert(::Type{G}, x::Leaf; allow_one=false) where G <: PGroup = convert(G, convert(BigInt, x); allow_one)

# Perhaps I could also use a let here
# It could be made threaad local
const EC_BUFFER = Vector{UInt8}(undef, 1000) # We can make it also thread local 
function convert(::Type{ECGroup{P}}, x::Node; allow_one=false) where P <: ECPoint

    L = bitlength(field(P))
    nbytes_field = cld(L, 8)  

    x_bytes = @view x[1].x[end-(nbytes_field-1):end]
    y_bytes = @view x[2].x[end-(nbytes_field-1):end]

    if all(iszero, x_bytes) && all(iszero, y_bytes)
        point_bytes = UInt8[0x00]
    else
        #buffer = Vector{UInt8}(undef, 1 + 2*nbytes_field)
        EC_BUFFER[1] = 0x04
        @inbounds copyto!(@view(EC_BUFFER[2:nbytes_field+1]), x_bytes)
        @inbounds copyto!(@view(EC_BUFFER[nbytes_field+2:2nbytes_field+1]), y_bytes)
        
        point_bytes = @view EC_BUFFER[1:2nbytes_field+1]
        #point_bytes = UInt8[0x04; x_bytes; y_bytes]
    end

    return convert(ECGroup{P}, point_bytes; allow_one)
end

function Tree(g::G; L = bitlength(G)) where G <: ECGroup

    nbytes_field = cld(L, 8)  # Using cld instead of div(x, y, RoundUp) 
    nbytes_spec = cld(L + 1, 8)
    
    bytes = octet(g)

    if iszero(bytes[1])

        leaf = Leaf(zeros(UInt8, nbytes_spec))
        return Tree((leaf, leaf))

    end

    @views x_bytes = bytes[2:nbytes_field + 1]
    @views y_bytes = bytes[nbytes_field + 2:end]

    if nbytes_spec == nbytes_field

        gxleaf = Leaf(x_bytes)
        gyleaf = Leaf(y_bytes)

    elseif nbytes_spec == nbytes_field + 1 # This is such an unfortunate oversight in the specification
        
        gxleaf = Leaf(UInt8[0x00; x_bytes])
        gyleaf = Leaf(UInt8[0x00; y_bytes])

    end
        
    return Tree((gxleaf, gyleaf))
end

function Tree(x::Vector{<:Group})
    L = bitlength(x[1])
    s = Tree[Tree(i, L = L) for i in x]
    return Node(s)
end

function marshal(x::PGroup)

    java_name = "com.verificatum.arithm.ModPGroup"
    p = modulus(x)
    q = order(x)
    g = Tree(x)
    e = UInt32(1)

    msg = (java_name, (p, q, g, e))

    tree = Tree(msg)

    return tree
end

# A bit verbose; I could instead read all curve specifications and retrieve the NIST name
function normalize_ecgroup_name(x::String)
    name = replace(x, "_"=>"-")

    lcase = lowercase(name)

    if lcase == "prime192v1"
        return "P-192"
    elseif lcase == "secp224r1"
        return "P-224"
    elseif lcase == "prime256v1"
        return "P-256"
    elseif lcase == "secp384r1"
        return "P-384"
    elseif lcase == "secp521r1"
        return "P-521"
    else
        return name
    end

end

normalize_ecgroup_name(x::Symbol) = normalize_ecgroup_name(String(x))

function marshal(g::ECGroup)

    java_name = "com.verificatum.arithm.ECqPGroup"

    # generator is not a group
    # @check spec(g) == spec(name(g)) "wrong group name"

    v_name = normalize_ecgroup_name(name(g))

    msg = (java_name, v_name)

    tree = Tree(msg)

    return tree
end

function unmarshal(tree::Tree)
    
    group_type = convert(String, tree.x[1])

    if group_type == "com.verificatum.arithm.ModPGroup"
        return _unmarshal_pgroup(tree.x[2])
    elseif group_type == "com.verificatum.arithm.ECqPGroup"
        return _unmarshal_ecgroup(tree.x[2])
    else
        error("Unrecognized group type: $group_type")
    end
end

function _unmarshal_pgroup(x::Node) 

    (p, q, g, e) = convert(Tuple{BigInt, BigInt, BigInt, UInt32}, x)
    
    G = concretize_type(PGroup, p, q)
    x = G(g)
    
    return x
end

spec_name(x::String) = Symbol(replace(x, "-"=>"_"))

function _unmarshal_ecgroup(x::Leaf)
    
    group_spec_str = convert(String, x)
    name = spec_name(group_spec_str)

    group_spec = spec(name)
    G = concretize_type(ECGroup, group_spec; name)
    g = G(generator(group_spec))

    return g
end


function convert(::Type{Vector{ElGamalRow{G, 1}}}, tree::Node; allow_one=false) where G <: Group

    a_tree, b_tree = tree.x
    𝐚 = convert(Vector{G}, a_tree; allow_one)
    𝐛 = convert(Vector{G}, b_tree; allow_one)
    𝐞 = [ElGamalRow(ai, bi) for (ai, bi) in zip(𝐚, 𝐛)]

    return 𝐞
end


function convert(::Type{Vector{ElGamalRow{G, N}}}, tree::Node; allow_one=false) where {G <: Group, N}

    𝐚 = ntuple(n -> convert(Vector{G}, tree[1][n]; allow_one), N)
    𝐛 = ntuple(n -> convert(Vector{G}, tree[2][n]; allow_one), N)

    𝐞 = [ElGamalRow(ai, bi) for (ai, bi) in zip(zip(𝐚...), zip(𝐛...))]
    
    return 𝐞
end

function convert(::Type{ElGamalRow{G, 1}}, tree::Node; allow_one=false) where G <: Group

    a_tree, b_tree = tree.x

    a = convert(G, a_tree; allow_one)
    b = convert(G, b_tree; allow_one)
    
    return ElGamalRow(a, b)
end

convert(::Type{NTuple{N, G}}, tree::Node; allow_one=false) where {G <: Group, N} = ntuple(n -> convert(G, tree[n]; allow_one), N)

convert(::Type{NTuple{N, BigInt}}, tree::Node) where N = ntuple(n -> convert(BigInt, tree[n]), N)
convert(::Type{NTuple{1, BigInt}}, tree::Leaf) = tuple(convert(BigInt, tree))
    
function convert(::Type{ElGamalRow{G, N}}, tree::Node; allow_one=false) where {G <: Group, N}

    a_tree, b_tree = tree.x

    a = convert(NTuple{N, G}, a_tree; allow_one)
    b = convert(NTuple{N, G}, b_tree; allow_one)
    
    return ElGamalRow(a, b)
end

function Tree(row::ElGamalRow{<:Group, 1})

    (; a, b) = row[1]

    return Tree((a, b))
end

function Tree(row::ElGamalRow{<:Group, N}) where N

    a = ntuple(n -> row[n].a, N)
    b = ntuple(n -> row[n].b, N)

    return Tree((a, b))
end


function Tree(𝐞::Vector{<:ElGamalRow{<:Group, 1}})

    𝐚 = [i[1].a for i in 𝐞]
    𝐛 = [i[1].b for i in 𝐞]

    tree = Tree((𝐚, 𝐛))
    
    return tree
end

function Tree(𝐞::Vector{<:ElGamalRow{<:Group, N}}) where N

    𝐚 = ntuple(n -> [i[n].a for i in 𝐞], N)
    𝐛 = ntuple(n -> [i[n].b for i in 𝐞], N)

    tree = Tree((𝐚, 𝐛))

    return tree
end

# The width would be extracted from the tree
function Tree(e::Vector{<:NTuple{1, <:Group}})
    return Tree(first.(e))
end

function convert(::Type{Vector{NTuple{1, G}}}, tree::Node) where G <: Group

    vec = convert(Vector{G}, tree)

    return [(i, ) for i in vec]
end


function marshal_publickey(y::G, g::G) where G <: Group
    
    group_spec = marshal(g)
    
    L = bitlength(G) # 
    
    g_tree = Tree(g; L)
    y_tree = Tree(y; L)

    public_key = Tree((g_tree, y_tree))
    tree = Tree((group_spec, public_key))

    return tree
end


# TOOD: change return order
function unmarshal_publickey(tree::Tree; relative::Bool = false)
    
    g = unmarshal(tree.x[1])
    G = typeof(g)

    g′, y = convert(Tuple{G, G}, tree.x[2]) 

    if !relative
        @check g′ == g "Generator does not match specification of the group. Perhaps intentioanl, if so pass `relative=true` as keyword argument."
    end

    return y, g′
end

function marshal_privatekey(g::Group, s::BigInt) 
    group_spec = marshal(g)

    @check 2 < s < order(g) - 1 "Secret key must be with in the order of the group"

    sleaf = Tree(s; L = bitlength(g)) # The leaf constructor could be improved, but for now this shall work fine

    tree = Tree((group_spec, sleaf))

    return tree
end


function unmarshal_privatekey(tree::Tree)

    g = unmarshal(tree.x[1])
    s = convert(BigInt, tree.x[2])    

    return (s, g) ### The group can often be omited when not needed.
end

# Returns the depth of the tree
function depth(tree::Tree)

    if tree isa Leaf
        return 0
    else
        return 1 + depth(tree[1])
    end

end

width_elgamal_row(::Type{<:PGroup}, tree::Tree) = depth(tree) == 1 ? 1 : length(tree[1])
width_elgamal_row(::Type{<:ECGroup}, tree::Tree) = depth(tree) == 2 ? 1 : length(tree[1])

width_elgamal_vec(::Type{<:PGroup}, tree::Tree) = depth(tree) == 2 ? 1 : length(tree[1])
width_elgamal_vec(::Type{<:ECGroup}, tree::Tree) = depth(tree) == 3 ? 1 : length(tree[1])

Tree(x::Vector{BigInt}; L = bitlength(maximum(x))) = Node([Leaf(i, L) for i in x])

export Tree, Node, Leaf, encode, decode, marshal, unmarshal

end
