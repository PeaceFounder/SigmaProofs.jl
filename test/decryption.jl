using Test

using CryptoGroups
import SigmaProofs.DecryptionProofs: prove, verify, decrypt, decryptinv
import SigmaProofs.Verificatum: ProtocolSpec
import SigmaProofs.ElGamal: Enc, ElGamalRow

g = @ECGroup{P_192}()
verifier = ProtocolSpec(; g)

𝐦 = [g^4, g^2, g^3]

sk = 123
pk = g^sk

encryptor = Enc(pk, g)

cyphertexts = encryptor(𝐦, rand(2:order(g)-1, length(𝐦))) .|> ElGamalRow

proposition = decrypt(g, cyphertexts, sk)
@test verify(proposition, sk) 

proof = prove(proposition, verifier, sk)
@test verify(proposition, proof, verifier)

# Higher order API
simulator = decrypt(g, cyphertexts, sk, verifier)
@test verify(simulator)

# Testing inverse

propositioninv = decryptinv(g, cyphertexts, sk)
@test verify(propositioninv, sk) 

proof = prove(propositioninv, verifier, sk)
@test verify(propositioninv, proof, verifier)

simulatorinv = decrypt(g, cyphertexts, sk, verifier)
@test verify(simulatorinv)
