import sys

from Crypto.Hash import RIPEMD160

data = bytes.fromhex(sys.argv[1])
hash_bytes = RIPEMD160.new(data).digest()
padded_hash = hash_bytes.rjust(32, b"\x00")
print(bytes.hex(padded_hash), end = '')
