using Test

using CryptoGroups
import SigmaProofs.DecryptionProofs: prove, verify, decrypt, decryptinv
import SigmaProofs.Verificatum: ProtocolSpec
import SigmaProofs.ElGamal: Enc

g = @ECGroup{P_192}()
verifier = ProtocolSpec(; g)

𝐦 = [g^4, g^2, g^3] .|> tuple

sk = 123
pk = g^sk

encryptor = Enc(pk, g)

ciphertexts = encryptor(𝐦, rand(2:order(g)-1, length(𝐦))) 

proposition = decrypt(g, ciphertexts, sk)
@test verify(proposition, sk) 

proof = prove(proposition, verifier, sk)
@test verify(proposition, proof, verifier)

# Higher order API
simulator = decrypt(g, ciphertexts, sk, verifier)
@test verify(simulator)

# Testing inverse

propositioninv = decryptinv(g, ciphertexts, sk)
@test verify(propositioninv, sk) 

proof = prove(propositioninv, verifier, sk)
@test verify(propositioninv, proof, verifier)

simulatorinv = decrypt(g, ciphertexts, sk, verifier)
@test verify(simulatorinv)
