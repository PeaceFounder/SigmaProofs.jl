module ElGamal

using CryptoGroups.Utils: @check
using CryptoGroups: Group
import Base: *, ^

width(x) = width(typeof(x))
width(T::Type) = error("Width is not implemented for $T")

width(::Type{NTuple{N, <:Group}}) where N = N
width(::Type{<:AbstractVector{<:NTuple{N, <:Group}}}) where N = N

struct ElGamalElement{G<:Group}
    a::G
    b::G
end

ElGamalElement(m::G) where G <: Group = ElGamalElement(one(G), m)

width(::Type{<:ElGamalElement}) = 1

*(x::ElGamalElement{G}, y::ElGamalElement{G}) where G <: Group = ElGamalElement(x.a * y.a, x.b * y.b)
*(x::ElGamalElement{G}, y::Tuple{G, G}) where G <: Group = x * ElGamalElement(y[1], y[2])
*(x::Tuple{G, G}, y::ElGamalElement{G}) where G <: Group = y * x

^(x::ElGamalElement{G}, k::Integer) where G <: Group = ElGamalElement(x.a ^ k, x.b ^ k) 

Base.isless(x::ElGamalElement{G}, y::ElGamalElement{G}) where G <: Group = x.a == y.a ? x.b < y.b : x.a == y.a

Base.:(==)(x::ElGamalElement{G}, y::ElGamalElement{G}) where G <: Group = x.a == y.a && x.b == y.b

struct ElGamalRow{G<:Group, N} 
    row::NTuple{N, ElGamalElement{G}}
end

ElGamalRow(a::G, b::G) where G <: Group = ElGamalRow(ElGamalElement(a, b))
ElGamalRow(a::NTuple{N, G}, b::NTuple{N, G}) where {N, G <: Group} = ElGamalRow{G, N}(ntuple(n -> ElGamalElement(a[n], b[n]), N))

ElGamalRow(row::NTuple{N, G}) where {N, G <: Group} = convert(ElGamalRow{G, N}, row)
ElGamalRow(element::ElGamalElement{G}) where {G <: Group} = convert(ElGamalRow{G, 1}, element)
ElGamalRow(row::AbstractVector{<:ElGamalElement{G}}) where {G <: Group} = convert(ElGamalRow{G}, row)

width(::Type{ElGamalRow{<:Group, N}}) where N = N
width(::Type{<:AbstractVector{<:ElGamalRow{<:Group, N}}}) where N = N

a(e::ElGamalRow{<:Group, N}) where N = ntuple(n -> e[n].a, N)
b(e::ElGamalRow{<:Group, N}) where N = ntuple(n -> e[n].b, N)

Base.convert(::Type{ElGamalRow{G, N}}, row::NTuple{N, G}) where {N, G<:Group} = ElGamalRow(tuple([ElGamalElement(mi) for mi in row]...))
Base.convert(::Type{ElGamalRow{G, 1}}, element::ElGamalElement{G}) where G <: Group = ElGamalRow((element,))
Base.convert(::Type{ElGamalRow{G}}, row::AbstractVector{<:ElGamalElement{G}}) where G <: Group = ElGamalRow(tuple(row...))
#Base.convert(::Type{ElGamalRow}, row) = ElGamalRow(row)

Base.:(==)(x::ElGamalRow{G, N}, y::ElGamalRow{G, N}) where {G <: Group, N} = x.row == y.row

Base.getindex(row::ElGamalRow, index::Integer) = row.row[index]
Base.getindex(row::ElGamalRow, range) = ElGamalRow(row.row[range])

Base.length(row::ElGamalRow) = length(row.row)
Base.lastindex(row::ElGamalRow) = length(row)

*(x::ElGamalRow{G}, y::ElGamalRow{G}) where G <: Group = ElGamalRow(x.row .* y.row)
*(x::ElGamalRow{G}, y::Tuple{G, G}) where G <: Group = ElGamalRow(x.row .* y)
*(x::Tuple{G, G}, y::ElGamalRow{G}) where G <: Group = y * x
*(x::ElGamalRow{G}, y::ElGamalElement{G}) where G <: Group = ElGamalRow(ElGamalElement{G}[i * y for i in x.row])
*(x::ElGamalElement{G}, y::ElGamalRow{G}) where G <: Group = y * x

^(x::ElGamalRow{G}, k::Integer) where G <: Group = ElGamalRow(x.row .^ k) #(x[1]^k, x[2]^k)

function Base.isless(x::ElGamalRow{G, N}, y::ElGamalRow{G, N}) where {G <: Group, N}

    for (xi, yi) in zip(x.row, y.row)

        if xi !== yi
            return xi < yi
        end

    end
    
    return false
end


struct Enc{T<:Group} 
    pk::T
    g::T
end

(enc::Enc)(r::Integer) = ElGamalElement(enc.g^r, enc.pk^r) # A tuple is treated as a scalar
(enc::Enc{G})(e::ElGamalElement{G}, r::Integer) where G <: Group = e * enc(r)
(enc::Enc{G})(m::G, r::Integer) where G <: Group = enc(ElGamalElement(one(G), m), r)
(enc::Enc{G})(m::AbstractVector{G}, r::AbstractVector{<:Integer}) where G <: Group = enc.(m, r) # Returns ElGamalElement vector
(enc::Enc{G})(m::AbstractVector{<:ElGamalElement{G}}, r::AbstractVector{<:Integer}) where G <: Group = enc.(m, r)

(enc::Enc)(r::NTuple{N, <:Integer}) where N = ElGamalRow(enc.(r))
(enc::Enc)(r::Vector{<:Integer}) = ElGamalRow(enc.(r))

(enc::Enc{G})(e::ElGamalRow{G}, r::Integer) where G <: Group = e * enc(r) # Tuple is treated as a scalar
(enc::Enc{G})(e::ElGamalRow{G}, r::NTuple{N, <:Integer}) where {N, G <: Group} = e * enc(r)
(enc::Enc{G})(m::NTuple{N, G}, r::Integer) where {N, G <: Group} = enc(ElGamalRow(m), r)
(enc::Enc{G})(m::NTuple{N, G}, r::NTuple{N, <:Integer}) where {N, G <: Group} = enc(ElGamalRow(m), r)

(enc::Enc{G})(m::AbstractVector{<:ElGamalRow{G}}, r::AbstractVector{<:Integer}) where G <: Group = enc.(m, r)
(enc::Enc{G})(m::AbstractVector{<:NTuple{N, G}}, r::AbstractVector{<:Integer}) where {N, G <: Group} = enc.(m, r)
(enc::Enc{G})(m::AbstractVector{<:ElGamalRow{G}}, r::AbstractVector{<:NTuple{N, <:Integer}}) where {N, G <: Group} = enc.(m, r)
(enc::Enc{G})(m::AbstractVector{<:NTuple{N, G}}, r::AbstractVector{<:NTuple{N, <:Integer}}) where {N, G <: Group} = enc.(m, r)


function (enc::Enc{G})(m::AbstractVector{<:ElGamalRow{G}}, r::AbstractMatrix{<:Integer}) where G <: Group

    @check size(r) == (length(m), width(m)) "Dimensions not equal"

    return [enc(mi, tuple(ri...)) for (mi, ri) in zip(m, eachrow(r))]
end

function (enc::Enc{G})(m::AbstractVector{<:NTuple{N, G}}, r::AbstractMatrix{<:Integer}) where {N, G <: Group}

    @check size(r) == (length(m), width(m)) "Dimensions not equal"
    
    return [enc(mi, tuple(ri...)) for (mi, ri) in zip(m, eachrow(r))]
end


struct Dec
    sk::Integer
end

(dec::Dec)(e::ElGamalElement) = e.b * e.a^(-dec.sk)
(dec::Dec)(e::ElGamalRow) = dec.(e.row)

(dec::Dec)(e::Tuple{G, G}) where G <: Group = dec(ElGamalElement(e.a, e.b))
(dec::Dec)(a::G, b::G) where G <: Group = dec(ElGamalElement(a, b))

(dec::Dec)(e::AbstractVector{<:ElGamalElement{<:Group}}) = dec.(e)
(dec::Dec)(e::AbstractVector{<:ElGamalRow{<:Group, N}}) where N = dec.(e) # Using this method over dot syntax offers more type safety 

end
