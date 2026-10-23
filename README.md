Ripdir is a powerful archiving tool that provides secure data preservation through authenticated encryption, content-defined chunking, deduplication, and signed runtime protections.

To use the program, you can build an archive or self-extracting executable by running the script with the `--pack` flag followed by your target directory, restore files using `--extract`, list contents with `--list`, and verify archive integrity with `--verify`.

(& much more)

It is open source and will always remain free to use. Please let us know what you think!

options:
  -h, --help            show this help message and exit
  
  --version             show program's version number and exit
  
  --pack DIRECTORY      Build a self-extracting archive
  
  --pack-raw DIRECTORY  Build a raw binary .ripdir archive
  
  --list                List authenticated archive contents
  
  --verify              Authenticate and verify all canonical file contents
  
  --extract DIRECTORY   Restore the archive under DIRECTORY/root-name
  
  --cat PATH            Decrypt a stored file to stdout
  
  --mount DIRECTORY     Mount the archive read-only using FUSE
  
  --repair OUTPUT       Verify and rebuild a Reed-Solomon-protected archive at OUTPUT
  
  --device-id           Print this installation's hashed device identifier for license policy setup
  
  --archive FILE        Archive to operate on
  
  --output FILE         Output path for --pack or --pack-raw
  
  --force               Replace an existing output
  
  --overwrite           Replace an existing extraction destination
  
  --strict-consistency  Abort if included source files or the source tree changes during packing
  
  --console-password    Use a terminal password prompt while packing
  
  --password-stdin      Read the password from standard input instead of prompting
  
  --console-mode        Force a Windows console in the generated executable
  
  --allow-unsafe-symlinks
                        Permit absolute or escaping symlink targets during extraction
                
  --generate-release-key FILE
                        Generate an encrypted Ed25519 signing key for protected executables
                        
  --generate-recipient-key PREFIX
                        Generate an encrypted recipient key pair
                        
  --recipient-key-type {x25519,rsa}
                        Key type for --generate-recipient-key
                        
  --recipient-pubkey PEM
                        Add a recipient public key to an archive; can be repeated
                        
  --recipient-key PEM   Unlock an archive with a recipient private key; can be repeated
  
  --recipient-only      Create an archive without a passphrase envelope; requires a recipient public key or --fido2-recipient
  
  --fido2-recipient     Enroll a FIDO2 authenticator PRF recipient; requires python-fido2 2.x and compatible hardware
  
  --redundancy          Add Reed-Solomon 8+2 shard protection; requires numpy and increases archive size
  
  --release-signing-key FILE
                        Private Ed25519 key used to sign a self-extracting executable
                        
  --bind-host           Bind the generated executable to this OS installation
  
  --anti-debug, --no-anti-debug
                        Enable best-effort runtime debugger/tracer detection in protected builds (enabled by default; use --no-anti-debug to opt out)
                        
  --license-endpoint HTTPS_URL
                        Require a signed short-lived lease from this HTTPS endpoint
                        
  --license-public-key HEX
                        Pinned 32-byte Ed25519 license-server public key as 64 hex characters
                        
  --serve-license HOST:PORT
                        Run the signed lease service; use behind a TLS reverse proxy
                        
  --backend-module PY   Server-only Python module exporting process(operation, payload, context)
  
  --backend-endpoint HTTPS_URL
                        Embed the HTTPS endpoint for server-side operations in a protected build
                        
  --backend-call OPERATION
                        Call an operation on the configured server-side backend
                        
  --payload-json JSON   JSON object/string/array payload for --backend-call
  
  --server-signing-key FILE
                        Private Ed25519 key used by --serve-license
                        
  --license-policy JSON
                        Policy JSON for --serve-license
