using Test
using CryptoGroups
using Random
using SigmaProofs.CommitmentShuffle: shuffle, commit, isbinding, verify, CommittedRow
using SigmaProofs: generator_basis
using SigmaProofs.Verificatum: ProtocolSpec

N = 3

G = @ECGroup{P_192}
g = G()

verifier = ProtocolSpec(; g)

basis = generator_basis(verifier, G, 10 * N)
shuffle!(basis) 

h = basis[1]
g1, g2, g3 = basis[2:4]

# Setting up a buletin board

𝐂 = G[] # Published imediatelly
𝛃 = BigInt[] # secret
rows = CommittedRow{G, G}[] # Published afterwards

function record(row, C, β)
    
    @test isbinding(row, C, h, β)
    @test verify(row, verifier)

    @test !any(x->x.g == row.g, rows) # all generators must be distinct
    
    push!(𝐂, C)
    push!(𝛃, β)
    push!(rows, row)

    return
end

# Some users commit on the messages

m1 = g^2
row1, C1, β1 = commit(m1, g1, h, verifier)
record(row1, C1, β1)

m2 = g^4
row2, C2, β2 = commit(m2, g2, h, verifier)
record(row2, C2, β2)

m3 = g^6
row3, C3, β3 = commit(m3, g3, h, verifier)
record(row3, C3, β3)

# Finally a shuffle can be constructed

simulator = shuffle(rows, h, 𝐂, 𝛃, verifier)
# The rows can be made public along with proof

@test verify(simulator) 

