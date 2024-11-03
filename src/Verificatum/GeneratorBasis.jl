module GeneratorBasis

using CryptoGroups.Utils: @check
using CryptoGroups: modulus, order, bitlength, Group, spec
using CryptoGroups.Specs: MODP, ECP
using CryptoPRG.Verificatum: PRG, RO, PRGIterator
using CryptoUtils: is_quadratic_residue #, sqrt_mod_prime

using BitIntegers

function modp_generator_basis(prg::PRG, p::Integer, q::Integer, N::Integer; nr::Integer = 0)

    np = bitlength(p)

    𝐭 = rand(prg, BigInt, N; n = np + nr)

    𝐭′ = mod.(𝐭, big(2)^(np + nr))

    𝐡 = powermod.(𝐭′, (p - 1) ÷ q, p)
    
    return 𝐡
end

modp_generator_basis(prg::PRG, spec::MODP, N::Integer; nr::Integer = 0) = modp_generator_basis(prg, modulus(spec), order(spec), N; nr)

using CryptoUtils: tonelli_shanks, hoc_sqrt

# https://github.com/fcasal/CryptoUtils.jl/issues/3
function sqrt_mod_prime(a::BigInt, p::BigInt)
    #a = mod(a, p)
    #is_quadratic_residue(a, p) || throw("$a is not a quadratic residue mod $p.")

    if p % 2 == 0
        return a

    elseif p % 4 == 3
        return powermod(a, div(p + 1, 4), p)

    elseif p % 8 == 5
        d = powermod(a, div(p - 1, 4), p)

        if d == 1
            r = powermod(a, div(p + 3, 8), p)
        elseif d == p - 1
            r = mod(2 * a * powermod(4 * a, div(p - 5, 8), p), p)
        end

        return r

    # If p-1 is of the form 2^k*s for large k, use tonelli-shanks.
    # Here k is large if k > 100
    elseif mod(p - 1, 1267650600228229401496703205376) == 0
        return tonelli_shanks(a, p)

    # depends on size of k
    else
        return hoc_sqrt(a, p)
    end
end

sqrt_mod_prime(a::Integer, b::Integer) = sqrt_mod_prime(BigInt(a), BigInt(b))

function bitint_type(nbits::Int)
    if nbits <= 256
        return UInt256
    elseif nbits <= 512
        return UInt512
    elseif nbits <= 1024
        return UInt1024
    else
        return BigInt
    end
end

function ecp_generator_basis(prg::PRG, (a, b)::Tuple{T, T}, p::T, q::T, N::Integer; nr::Integer = 0) where T <: Integer

    np = bitlength(p) # 1

    d = T(2)^(np + nr)
    
    U = bitint_type(np)
    up = U(p)

    𝐡 = Vector{Tuple{T, T}}(undef, N)

    l = 1

    f(x) = x^3 + a*x + b # This assumes that I do know how to do arithmetics with fields.

    for ti in PRGIterator{T}(prg, np + nr)

        ti′ = mod(ti, d)
        zi = mod(ti′, p)

        y2 = mod(f(zi), p)

        if is_quadratic_residue(U(y2), up)

            x = zi

            y = sqrt_mod_prime(y2, p)

            # The smallest root is taken
            if p - y < y
                y = p - y
            end

            𝐡[l] = (x, y)

            if l == N
                break
            else
                l += 1                
            end
        end
    end

    if l != N
        error("Not enough numbers for 𝐭 have been allocated")
    end

    return 𝐡
end

function ecp_generator_basis(prg::PRG, spec::ECP, N::Integer; nr::Integer = 0)
    (; a, b) = spec
    return ecp_generator_basis(prg, (a, b), modulus(spec), order(spec), N; nr)
end


# For pattern matching
_generator_basis(prg::PRG, spec::MODP, N::Integer; nr) = modp_generator_basis(prg, spec, N; nr)
_generator_basis(prg::PRG, spec::ECP, N::Integer; nr) = ecp_generator_basis(prg, spec, N; nr)

function generator_basis(prg::PRG, ::Type{G}, N::Integer; nr::Integer = 0) where G <: Group
    @check !isnothing(order(G)) "Order of the group must be known"
    _spec = spec(G)
    g_vec = _generator_basis(prg, _spec, N; nr)
    return G.(g_vec)
end

generator_basis(prg::PRG, ::Type{G}; nr::Integer = 0) where G <: Group = generator_basis(prg, G, 1; nr)[1]


end
