using SafeTestsets

@safetestset "Testing ElGamal" begin
    include("elgamal.jl")
end

@safetestset "Testing PGroup Generator Basis" begin
    include("Verificatum/gbasis.jl")
end

@safetestset "Testing ECGroup Generator Basis" begin
    include("Verificatum/gecbasis.jl")
    include("Verificatum/ecp_basis.jl")
end

@safetestset "Testing Generators" begin
    include("Verificatum/generators.jl")
end

@safetestset "Testing CRS" begin
    include("Verificatum/crs.jl")
end

@safetestset "Testing Parser" begin
    include("parser.jl")
end

@safetestset "Testing Parser Utils" begin
    include("Verificatum/rho.jl")
    include("Verificatum/io.jl")
end

@safetestset "Testing Decryption" begin
    include("decryption.jl")
end

@safetestset "Testing Secret Sharing" begin
    include("secretsharing.jl")
end

@safetestset "Testing Commitment Shuffle" begin
    include("shuffle.jl")
end

@safetestset "Testing Range Proofs" begin
    include("ranges.jl")
end

@safetestset "Example Vickrey Auction" begin
    include("../examples/auctions.jl")
end

@safetestset "Testing Serialization" begin
    include("serializer.jl")
end



