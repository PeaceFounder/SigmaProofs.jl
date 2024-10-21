using Test

using CryptoGroups
import SigmaProofs.DecryptionProofs: prove, verify, decrypt, decryptinv, Decryption, DecryptionInv
import SigmaProofs.Verificatum: ProtocolSpec
import SigmaProofs.ElGamal: Enc
import SigmaProofs.Serializer: load, save, digest
import SigmaProofs: Simulator
import CryptoPRG: HashSpec

g = @ECGroup{P_192}()
verifier = ProtocolSpec(; g)

𝐦 = [g^4, g^2, g^3] .|> tuple

sk = 123
pk = g^sk

encryptor = Enc(pk, g)

ciphertexts = encryptor(𝐦, rand(2:order(g)-1, length(𝐦)))

DECRYPT_DIR = joinpath(tempdir(), "decrypt")
rm(DECRYPT_DIR, recursive=true, force=true)
mkpath(DECRYPT_DIR)

simulator = decrypt(g, ciphertexts, sk, verifier)
save(simulator, DECRYPT_DIR)
loaded_simulator = load(Simulator{Decryption}, DECRYPT_DIR) # 

@test loaded_simulator == simulator
@test digest(simulator, HashSpec("sha256")) == digest(Simulator{Decryption}, DECRYPT_DIR, HashSpec("sha256"))

# ToDo: DecryptionInv

DECRYPTINV_DIR = joinpath(tempdir(), "decryptinv")
rm(DECRYPTINV_DIR, recursive=true, force=true)
mkpath(DECRYPTINV_DIR)

simulator = decryptinv(g, ciphertexts, sk, verifier)
save(simulator, DECRYPTINV_DIR)
loaded_simulator = load(Simulator{DecryptionInv}, DECRYPTINV_DIR) # 

@test loaded_simulator == simulator
@test digest(simulator, HashSpec("sha256")) == digest(Simulator{DecryptionInv}, DECRYPTINV_DIR, HashSpec("sha256"))
