#!/usr/bin/env python3
from __future__ import annotations
import argparse
import atexit
import base64
import getpass
import http.server
import hashlib
import hmac
import json
import ntpath
import os
import platform
import posixpath
import queue
import re
import secrets
import shutil
import sqlite3
import stat
import struct
import subprocess
import sys
import tempfile
import threading
import time
import zipfile
import zlib
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import BinaryIO,Callable,Dict,Iterator,List,Optional,Sequence,Set,Tuple
try:
    import zstandard as zstd
except ImportError:
    zstd=None
try:
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    from cryptography.hazmat.primitives.kdf.argon2 import Argon2id
    from cryptography.hazmat.primitives.kdf.hkdf import HKDF
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey,Ed25519PublicKey
    from cryptography.hazmat.primitives.asymmetric import x25519,rsa,padding
except ImportError as exc:
    raise SystemExit("ripdir requires cryptography >= 44.0") from exc
APP_NAME="ripdir"
FORMAT="ripdir-archive"
ARCHIVE_MAGIC=b"RIPDIRAR"
RECORD_MAGIC=b"RIPRECOR"
MANIFEST_MAGIC=b"RIPMANIF"
FOOTER_MAGIC=b"RIPEND__"
PAYLOAD_NAME="ripdir.payload"
HEADER_STRUCT=struct.Struct(">8sHI16s16sI14s")
RECORD_STRUCT=struct.Struct(">8sQIBIII")
MANIFEST_BLOCK_STRUCT=struct.Struct(">8sIII")
FOOTER_STRUCT=struct.Struct(">8sQQI32s32s32s")
HEADER_SIZE=HEADER_STRUCT.size
RECORD_SIZE=RECORD_STRUCT.size
MANIFEST_BLOCK_HEADER_SIZE=MANIFEST_BLOCK_STRUCT.size
FOOTER_SIZE=FOOTER_STRUCT.size
SALT_SIZE=16
ARCHIVE_ID_SIZE=16
KEY_SIZE=32
NONCE_SIZE=12
TAG_SIZE=16
CHUNK_SIZE=4*1024*1024
MIN_CHUNK_SIZE=256*1024
AVG_CHUNK_SIZE=1024*1024
MAX_ENVELOPE_BYTES=1024*1024
MAX_RECIPIENTS=128
REDUNDANCY_MAGIC=b"RIPRSPAR"
REDUNDANCY_HEADER_BASE=struct.Struct(">8sQIHHQ32s32s")
REDUNDANCY_HEADER=struct.Struct(">8sQIHHQ32s32sI4s")
REDUNDANCY_HEADER_SIZE=REDUNDANCY_HEADER.size
REDUNDANCY_HEADER_COPIES=2
REDUNDANCY_SHARD_SIZE=1024*1024
REDUNDANCY_DATA_SHARDS=8
REDUNDANCY_PARITY_SHARDS=2
REDUNDANCY_SHARD_COUNT=REDUNDANCY_DATA_SHARDS+REDUNDANCY_PARITY_SHARDS
REDUNDANCY_CHECKSUM_SIZE=32
MANIFEST_BLOCK_SIZE=1024*1024
MANIFEST_MAX_PLAIN_BLOCK=4*1024*1024
MANIFEST_MAX_CIPHER_BLOCK=8*1024*1024
MAX_PATH_BYTES=32768
ARGON2_MEMORY_KIB=64*1024
ARGON2_ITERATIONS=3
ARGON2_LANES=4
RECORD_FLAG_ZLIB=0x01
RECORD_FLAG_ZSTD=0x02
RECORD_FLAG_REFERENCE=0x04
KNOWN_RECORD_FLAGS=RECORD_FLAG_ZLIB|RECORD_FLAG_ZSTD|RECORD_FLAG_REFERENCE
ProgressCallback=Callable[[int,int,str],None]
_ZIP_PAYLOAD_TEMP:Optional[str]=None
SIGNATURE_SIDECAR_SUFFIX=".sig"
SIGNATURE_SIZE=64
NATIVE_TRAILER_MAGIC=b"RIPNATIV"
NATIVE_TRAILER_STRUCT=struct.Struct(">8sQ")
RELEASE_SIGNATURE_CONTEXT=b"ripdir release integrity\x00"
LICENSE_SIGNATURE_CONTEXT=b"ripdir license lease\x00"
TRUSTED_RELEASE_PUBLIC_KEY_HEX=""
TRUSTED_MACHINE_BINDING_HEX=""
RUNTIME_ANTI_DEBUG=False
LICENSE_ENDPOINT=""
TRUSTED_LICENSE_PUBLIC_KEY_HEX=""
BACKEND_ENDPOINT=""
_ACTIVE_LEASE:Optional[Dict[str,object]]=None
class CancelledError(RuntimeError):
    pass
class GuiUnavailable(RuntimeError):
    pass
def canonical_json(value:object)->bytes:
    return json.dumps(value,ensure_ascii=False,sort_keys=True,separators=(",",":")).encode("utf-8")
def password_gui(confirm:bool=False)->Optional[str]:
    try:
        import tkinter as tk
        from tkinter import messagebox,simpledialog
        root=tk.Tk()
    except Exception as exc:
        raise GuiUnavailable("Tk GUI is unavailable") from exc
    root.withdraw()
    try:
        for _ in range(3):
            value=simpledialog.askstring(APP_NAME,"Enter archive password:",show="*",parent=root)
            if value is None:
                return None
            if not value:
                messagebox.showwarning(APP_NAME,"Password must not be empty.",parent=root)
                continue
            if confirm:
                second=simpledialog.askstring(APP_NAME,"Confirm archive password:",show="*",parent=root)
                if second is None:
                    return None
                if value!=second:
                    messagebox.showerror(APP_NAME,"Passwords do not match.",parent=root)
                    continue
            return value
        return None
    finally:
        root.destroy()
def password_stdin(confirm:bool=False)->Optional[str]:
    try:
        value=sys.stdin.readline()
    except (EOFError,KeyboardInterrupt):
        return None
    if not value:
        return None
    value=value.rstrip("\r\n")
    if not value:
        raise ValueError("Password must not be empty")
    if confirm:
        try:
            second=sys.stdin.readline()
        except (EOFError,KeyboardInterrupt):
            return None
        if not second:
            return None
        second=second.rstrip("\r\n")
        if value!=second:
            raise ValueError("Passwords do not match")
    return value
def get_password(confirm:bool=False,prefer_gui:bool=False,stdin:bool=False)->Optional[str]:
    if stdin:
        return password_stdin(confirm)
    if prefer_gui:
        try:
            value=password_gui(confirm)
        except GuiUnavailable:
            value=None
        else:
            if value is not None:
                return value
            return None
    try:
        value=getpass.getpass(f"{APP_NAME} password: ")
    except (EOFError,KeyboardInterrupt):
        return None
    if not value:
        raise ValueError("Password must not be empty")
    if confirm:
        second=getpass.getpass("Confirm password: ")
        if value!=second:
            raise ValueError("Passwords do not match")
    return value
def password_wrap_key(password:str,salt:bytes,archive_id:bytes)->bytes:
    if not password:
        raise ValueError("Password must not be empty")
    raw=Argon2id(salt=salt,length=KEY_SIZE,iterations=ARGON2_ITERATIONS,lanes=ARGON2_LANES,memory_cost=ARGON2_MEMORY_KIB).derive(password.encode("utf-8"))
    return HKDF(algorithm=hashes.SHA256(),length=KEY_SIZE,salt=None,info=b"ripdir passphrase envelope"+archive_id).derive(raw)
def derive_keys(master_key:bytes,archive_id:bytes)->Dict[str,bytes]:
    if len(master_key)!=KEY_SIZE or len(archive_id)!=ARCHIVE_ID_SIZE:
        raise ValueError("Invalid archive master key material")
    labels=("payload","metadata","header-mac","index","dedup","repair")
    return {label:HKDF(algorithm=hashes.SHA256(),length=KEY_SIZE,salt=archive_id,info=b"ripdir key separation "+label.encode("ascii")).derive(master_key) for label in labels}
def _b64(data:bytes)->str:
    return base64.b64encode(data).decode("ascii")
def _unb64(value:object,expected:Optional[int]=None)->bytes:
    if not isinstance(value,str):
        raise ValueError("Malformed key envelope field")
    raw=base64.b64decode(value,validate=True)
    if expected is not None and len(raw)!=expected:
        raise ValueError("Malformed key envelope field length")
    return raw
def _recipient_key_id(public_key:object)->str:
    if isinstance(public_key,x25519.X25519PublicKey):
        raw=public_key.public_bytes(serialization.Encoding.Raw,serialization.PublicFormat.Raw)
    elif isinstance(public_key,rsa.RSAPublicKey):
        raw=public_key.public_bytes(serialization.Encoding.DER,serialization.PublicFormat.SubjectPublicKeyInfo)
    else:
        raise ValueError("Recipient keys must be X25519 or RSA public keys")
    return hashlib.sha256(raw).hexdigest()
def _load_public_key(path:str):
    try:
        key=serialization.load_pem_public_key(Path(path).read_bytes())
    except Exception as exc:
        raise ValueError(f"Cannot load recipient public key {path}: {exc}") from exc
    if isinstance(key,rsa.RSAPublicKey) and key.key_size<2048:
        raise ValueError("RSA recipient keys must be at least 2048 bits")
    if not isinstance(key,(x25519.X25519PublicKey,rsa.RSAPublicKey)):
        raise ValueError(f"Unsupported recipient key type in {path}; use X25519 or RSA")
    return key
def _load_private_key(path:str):
    encoded=Path(path).read_bytes()
    try:
        key=serialization.load_pem_private_key(encoded,password=None)
    except TypeError:
        try:
            password=getpass.getpass(f"Private-key password for {path}: ")
        except (EOFError,KeyboardInterrupt):
            raise ValueError("Private-key unlock cancelled")
        key=serialization.load_pem_private_key(encoded,password=password.encode("utf-8"))
    except ValueError as exc:
        raise ValueError(f"Cannot load recipient private key {path}: {exc}") from exc
    if not isinstance(key,(x25519.X25519PrivateKey,rsa.RSAPrivateKey)):
        raise ValueError(f"Unsupported recipient private key type in {path}; use X25519 or RSA")
    if isinstance(key,rsa.RSAPrivateKey) and key.key_size<2048:
        raise ValueError("RSA recipient keys must be at least 2048 bits")
    return key
FIDO2_RP_ID="ripdir.local"
FIDO2_ORIGIN="https://ripdir.local"
class RipdirFidoInteraction:
    def prompt_up(self)->None:
        print("Touch or unlock your FIDO2 authenticator when prompted.",file=sys.stderr)
    def request_pin(self,permissions,rp_id):
        return getpass.getpass(f"FIDO2 PIN for {rp_id or FIDO2_RP_ID}: ")
    def request_uv(self,permissions,rp_id)->bool:
        return True
def _fido_field(value,field:str):
    if isinstance(value,dict):
        return value.get(field)
    return getattr(value,field,None)
def _fido2_prf(salt:bytes,credential_id:Optional[bytes]=None,enroll:bool=False)->Tuple[bytes,Optional[bytes]]:
    if len(salt)!=32:
        raise ValueError("FIDO2 PRF salt must be 32 bytes")
    try:
        from fido2.client import Fido2Client,DefaultClientDataCollector
        from fido2.hid import CtapHidDevice
        from fido2.ctap2.extensions import HmacSecretExtension
    except ImportError as exc:
        raise RuntimeError("FIDO2 PRF support requires python-fido2 2.x") from exc
    devices=list(CtapHidDevice.list_devices())
    if not devices:
        raise RuntimeError("No FIDO2 HID authenticator was found")
    try:
        interaction=RipdirFidoInteraction()
        collector=DefaultClientDataCollector(FIDO2_ORIGIN)
        client=Fido2Client(devices[0],collector,user_interaction=interaction,extensions=[HmacSecretExtension()])
        if enroll:
            creation={"rp":{"id":FIDO2_RP_ID,"name":"ripdir"},"user":{"id":secrets.token_bytes(16),"name":"ripdir-recipient","displayName":"ripdir archive recipient"},"challenge":secrets.token_bytes(32),"pubKeyCredParams":[{"type":"public-key","alg":-7},{"type":"public-key","alg":-257}],"timeout":120000,"attestation":"none","authenticatorSelection":{"authenticatorAttachment":"cross-platform","userVerification":"required"},"extensions":{"prf":{"eval":{"first":salt}}}}
            registration=client.make_credential(creation)
            credential_id=bytes(registration.raw_id)
        elif credential_id is None:
            raise ValueError("FIDO2 unlock requires an archive credential identifier")
        request={"challenge":secrets.token_bytes(32),"rpId":FIDO2_RP_ID,"allowCredentials":[{"type":"public-key","id":credential_id}],"timeout":120000,"userVerification":"required","extensions":{"prf":{"eval":{"first":salt}}}}
        selection=client.get_assertion(request)
        response=selection.get_response(0) if hasattr(selection,"get_response") else selection
        extension_results=getattr(response,"client_extension_results",None)
        if extension_results is None:
            extension_results=getattr(selection,"extension_results",None)
        prf_output=_fido_field(extension_results,"prf")
        results=_fido_field(prf_output,"results")
        first=_fido_field(results,"first")
        if not isinstance(first,(bytes,bytearray)) or len(first)<32:
            raise RuntimeError("Authenticator did not return a usable PRF result; verify FIDO2 PRF support and user verification")
        return bytes(first),credential_id
    finally:
        for opened in devices:
            try:
                opened.close()
            except Exception:
                pass
def _fido2_wrap_key(prf_output:bytes,archive_id:bytes,credential_id:bytes)->bytes:
    return HKDF(algorithm=hashes.SHA256(),length=KEY_SIZE,salt=archive_id,info=b"ripdir FIDO2 PRF envelope"+credential_id).derive(prf_output)
def create_key_envelope(master_key:bytes,password:Optional[str],salt:bytes,archive_id:bytes,recipient_public_paths:Sequence[str],fido2_recipient:bool=False)->bytes:
    recipients=[]
    if password is not None:
        wrapping_key=password_wrap_key(password,salt,archive_id)
        nonce=secrets.token_bytes(NONCE_SIZE)
        wrapped=AESGCM(wrapping_key).encrypt(nonce,master_key,b"ripdir passphrase envelope"+archive_id)
        recipients.append({"type":"passphrase","nonce":_b64(nonce),"wrapped":_b64(wrapped)})
    if len(recipient_public_paths)>MAX_RECIPIENTS:
        raise ValueError(f"At most {MAX_RECIPIENTS} recipient keys are supported")
    seen=set()
    for path in recipient_public_paths:
        public_key=_load_public_key(path)
        key_id=_recipient_key_id(public_key)
        if key_id in seen:
            raise ValueError(f"Duplicate recipient public key: {path}")
        seen.add(key_id)
        if isinstance(public_key,x25519.X25519PublicKey):
            ephemeral=x25519.X25519PrivateKey.generate()
            ephemeral_public=ephemeral.public_key().public_bytes(serialization.Encoding.Raw,serialization.PublicFormat.Raw)
            shared=ephemeral.exchange(public_key)
            wrapping_key=HKDF(algorithm=hashes.SHA256(),length=KEY_SIZE,salt=archive_id,info=b"ripdir X25519 recipient envelope"+bytes.fromhex(key_id)).derive(shared)
            nonce=secrets.token_bytes(NONCE_SIZE)
            aad=b"ripdir X25519 envelope"+archive_id+bytes.fromhex(key_id)+ephemeral_public
            wrapped=AESGCM(wrapping_key).encrypt(nonce,master_key,aad)
            recipients.append({"type":"x25519","key_id":key_id,"ephemeral":_b64(ephemeral_public),"nonce":_b64(nonce),"wrapped":_b64(wrapped)})
        elif isinstance(public_key,rsa.RSAPublicKey):
            wrapped=public_key.encrypt(master_key,padding.OAEP(mgf=padding.MGF1(algorithm=hashes.SHA256()),algorithm=hashes.SHA256(),label=b"ripdir RSA envelope"+archive_id))
            recipients.append({"type":"rsa-oaep-sha256","key_id":key_id,"wrapped":_b64(wrapped)})
    if fido2_recipient:
        fido_salt=secrets.token_bytes(32)
        prf_output,credential_id=_fido2_prf(fido_salt,enroll=True)
        if credential_id is None:
            raise RuntimeError("FIDO2 registration did not return a credential identifier")
        wrapping_key=_fido2_wrap_key(prf_output,archive_id,credential_id)
        nonce=secrets.token_bytes(NONCE_SIZE)
        aad=b"ripdir FIDO2 envelope"+archive_id+credential_id+fido_salt+FIDO2_RP_ID.encode("ascii")
        wrapped=AESGCM(wrapping_key).encrypt(nonce,master_key,aad)
        recipients.append({"type":"fido2-prf","rp_id":FIDO2_RP_ID,"credential_id":_b64(credential_id),"salt":_b64(fido_salt),"nonce":_b64(nonce),"wrapped":_b64(wrapped)})
    if not recipients:
        raise ValueError("At least one passphrase, FIDO2 authenticator, or recipient public key is required")
    envelope=canonical_json({"format":"ripdir-key-envelope","recipients":recipients})
    if len(envelope)>MAX_ENVELOPE_BYTES:
        raise ValueError("Key envelope exceeds the size limit")
    return envelope
def _unlock_pkcs11_rsa(uri:str,recipients:Sequence[object],archive_id:bytes)->Optional[bytes]:
    try:
        import pkcs11
        from pkcs11 import Attribute,ObjectClass,KeyType,Mechanism,MGF
    except ImportError as exc:
        raise RuntimeError("PKCS#11 recipient support requires python-pkcs11") from exc
    parsed=urllib.parse.urlparse(uri)
    if parsed.scheme.lower()!="pkcs11":
        return None
    module_path=urllib.parse.unquote(parsed.path or parsed.netloc)
    parameters=urllib.parse.parse_qs(parsed.query,strict_parsing=True)
    token_label=(parameters.get("token") or [None])[0]
    key_label=(parameters.get("label") or [None])[0]
    if not module_path or not token_label or not key_label:
        raise ValueError("PKCS#11 recipient URI must be pkcs11:/path/to/module.so?token=TOKEN_LABEL&label=KEY_LABEL")
    pin=getpass.getpass(f"PIN for PKCS#11 token {token_label}: ")
    library=pkcs11.lib(module_path)
    token=library.get_token(token_label=token_label)
    with token.open(user_pin=pin) as session:
        public=session.get_key(label=key_label,object_class=ObjectClass.PUBLIC_KEY,key_type=KeyType.RSA)
        modulus=bytes(public[Attribute.MODULUS])
        exponent=bytes(public[Attribute.PUBLIC_EXPONENT])
        crypto_public=rsa.RSAPublicNumbers(int.from_bytes(exponent,"big"),int.from_bytes(modulus,"big")).public_key()
        if crypto_public.key_size<2048:
            raise ValueError("PKCS#11 RSA recipient keys must be at least 2048 bits")
        key_id=_recipient_key_id(crypto_public)
        envelope=None
        for candidate in recipients:
            if isinstance(candidate,dict) and candidate.get("type")=="rsa-oaep-sha256" and candidate.get("key_id")==key_id:
                envelope=candidate
                break
        if envelope is None:
            return None
        private=session.get_key(label=key_label,object_class=ObjectClass.PRIVATE_KEY,key_type=KeyType.RSA)
        wrapped=_unb64(envelope.get("wrapped"))
        label=b"ripdir RSA envelope"+archive_id
        try:
            master=private.decrypt(wrapped,mechanism=Mechanism.RSA_PKCS_OAEP,mechanism_param=(Mechanism.SHA256,MGF.SHA256,label))
        except Exception as exc:
            raise ValueError(f"PKCS#11 token could not decrypt the archive key: {exc}") from exc
        if len(master)!=KEY_SIZE:
            raise ValueError("PKCS#11 token returned an invalid archive key")
        return master
def unlock_master_key(envelope_bytes:bytes,password:Optional[str],salt:bytes,archive_id:bytes,recipient_private_paths:Sequence[str])->bytes:
    if len(envelope_bytes)>MAX_ENVELOPE_BYTES:
        raise ValueError("Key envelope exceeds the size limit")
    try:
        envelope=json.loads(envelope_bytes.decode("utf-8"))
    except Exception as exc:
        raise ValueError("Malformed key envelope") from exc
    recipients=envelope.get("recipients") if isinstance(envelope,dict) else None
    if not isinstance(envelope,dict) or envelope.get("format")!="ripdir-key-envelope" or not isinstance(recipients,list) or not 1<=len(recipients)<=MAX_RECIPIENTS+2:
        raise ValueError("Invalid key envelope structure")
    errors=[]
    if password is not None:
        for item in recipients:
            if not isinstance(item,dict) or item.get("type")!="passphrase":
                continue
            try:
                wrapping_key=password_wrap_key(password,salt,archive_id)
                nonce=_unb64(item.get("nonce"),NONCE_SIZE)
                wrapped=_unb64(item.get("wrapped"),KEY_SIZE+TAG_SIZE)
                master=AESGCM(wrapping_key).decrypt(nonce,wrapped,b"ripdir passphrase envelope"+archive_id)
                if len(master)!=KEY_SIZE:
                    raise ValueError("Invalid master-key length")
                return master
            except Exception as exc:
                errors.append(exc)
                break
    for path in recipient_private_paths:
        if str(path).lower() in {"fido2","fido2:"}:
            for item in recipients:
                if not isinstance(item,dict) or item.get("type")!="fido2-prf":
                    continue
                try:
                    credential_id=_unb64(item.get("credential_id"))
                    fido_salt=_unb64(item.get("salt"),32)
                    nonce=_unb64(item.get("nonce"),NONCE_SIZE)
                    wrapped=_unb64(item.get("wrapped"),KEY_SIZE+TAG_SIZE)
                    rp_id=item.get("rp_id")
                    if rp_id!=FIDO2_RP_ID:
                        raise ValueError("Unsupported FIDO2 relying-party identifier")
                    prf_output,_=_fido2_prf(fido_salt,credential_id=credential_id,enroll=False)
                    wrapping_key=_fido2_wrap_key(prf_output,archive_id,credential_id)
                    aad=b"ripdir FIDO2 envelope"+archive_id+credential_id+fido_salt+FIDO2_RP_ID.encode("ascii")
                    master=AESGCM(wrapping_key).decrypt(nonce,wrapped,aad)
                    if len(master)!=KEY_SIZE:
                        raise ValueError("Invalid master-key length")
                    return master
                except Exception as exc:
                    errors.append(exc)
            continue
        if str(path).lower().startswith("pkcs11:"):
            master=_unlock_pkcs11_rsa(str(path),recipients,archive_id)
            if master is not None:
                return master
            continue
        private_key=_load_private_key(path)
        public_key=private_key.public_key()
        key_id=_recipient_key_id(public_key)
        for item in recipients:
            if not isinstance(item,dict) or item.get("key_id")!=key_id:
                continue
            try:
                kind=item.get("type")
                if kind=="x25519" and isinstance(private_key,x25519.X25519PrivateKey):
                    ephemeral_raw=_unb64(item.get("ephemeral"),32)
                    ephemeral=x25519.X25519PublicKey.from_public_bytes(ephemeral_raw)
                    shared=private_key.exchange(ephemeral)
                    wrapping_key=HKDF(algorithm=hashes.SHA256(),length=KEY_SIZE,salt=archive_id,info=b"ripdir X25519 recipient envelope"+bytes.fromhex(key_id)).derive(shared)
                    nonce=_unb64(item.get("nonce"),NONCE_SIZE)
                    wrapped=_unb64(item.get("wrapped"),KEY_SIZE+TAG_SIZE)
                    aad=b"ripdir X25519 envelope"+archive_id+bytes.fromhex(key_id)+ephemeral_raw
                    master=AESGCM(wrapping_key).decrypt(nonce,wrapped,aad)
                elif kind=="rsa-oaep-sha256" and isinstance(private_key,rsa.RSAPrivateKey):
                    wrapped=_unb64(item.get("wrapped"))
                    master=private_key.decrypt(wrapped,padding.OAEP(mgf=padding.MGF1(algorithm=hashes.SHA256()),algorithm=hashes.SHA256(),label=b"ripdir RSA envelope"+archive_id))
                else:
                    continue
                if len(master)!=KEY_SIZE:
                    raise ValueError("Invalid master-key length")
                return master
            except Exception as exc:
                errors.append(exc)
    raise ValueError("Password or recipient private key did not unlock this archive")
def derive_data_nonce(data_key:bytes,archive_id:bytes,file_number:int,chunk_index:int)->bytes:
    message=b"ripdir data nonce"+archive_id+struct.pack(">QQ",file_number,chunk_index)
    return hmac.new(data_key,message,hashlib.sha256).digest()[:NONCE_SIZE]
def derive_manifest_nonce(manifest_key:bytes,archive_id:bytes,block_index:int)->bytes:
    message=b"ripdir manifest nonce"+archive_id+struct.pack(">Q",block_index)
    return hmac.new(manifest_key,message,hashlib.sha256).digest()[:NONCE_SIZE]
def build_header(salt:bytes,archive_id:bytes,envelope_length:int)->bytes:
    if len(salt)!=SALT_SIZE or len(archive_id)!=ARCHIVE_ID_SIZE:
        raise ValueError("Invalid archive key material")
    if not 1<=envelope_length<=MAX_ENVELOPE_BYTES:
        raise ValueError("Invalid key envelope length")
    return HEADER_STRUCT.pack(ARCHIVE_MAGIC,0,CHUNK_SIZE,salt,archive_id,envelope_length,b"\0"*14)
def parse_header(data:bytes)->Dict[str,object]:
    if len(data)!=HEADER_SIZE:
        raise ValueError("Archive header is truncated")
    magic,flags,chunk_size,salt,archive_id,envelope_length,reserved=HEADER_STRUCT.unpack(data)
    if magic!=ARCHIVE_MAGIC:
        raise ValueError("Invalid ripdir archive magic")
    if flags!=0 or reserved!=b"\0"*14:
        raise ValueError("Unsupported archive header flags")
    if chunk_size!=CHUNK_SIZE:
        raise ValueError("Unsupported archive chunk size")
    if not 1<=envelope_length<=MAX_ENVELOPE_BYTES:
        raise ValueError("Invalid key envelope length")
    return {"flags":flags,"chunk_size":chunk_size,"salt":salt,"archive_id":archive_id,"envelope_length":envelope_length,"raw":data}
def normalize_path(path:str)->str:
    if not isinstance(path,str) or not path:
        raise ValueError("Archive path is empty")
    if "\0" in path:
        raise ValueError("Archive path contains NUL")
    if os.name=="nt":
        path=path.replace("\\","/")
    if path.startswith("/"):
        raise ValueError(f"Unsafe archive path: {path}")
    parts=path.split("/")
    if any(part in ("",".","..") for part in parts):
        raise ValueError(f"Unsafe archive path: {path}")
    if parts[0].endswith(":"):
        raise ValueError(f"Drive-qualified archive path: {path}")
    if len(path.encode("utf-8"))>MAX_PATH_BYTES:
        raise ValueError("Archive path is too long")
    return "/".join(parts)
def validate_host_component(path:str)->None:
    if os.name!="nt":
        return
    for component in path.split("/"):
        if not component or component.endswith(("."," ")):
            raise ValueError(f"Path cannot be represented on Windows: {path}")
        if any(ord(char)<32 or char in '<>:\\"|?*' for char in component):
            raise ValueError(f"Path cannot be represented on Windows: {path}")
        stem=component.split(".",1)[0].upper()
        if stem in {"CON","PRN","AUX","NUL",*(f"COM{i}" for i in range(1,10)),*(f"LPT{i}" for i in range(1,10))}:
            raise ValueError(f"Reserved Windows path component: {path}")
def create_staging_db(prefix:str="ripdir-tree-")->Tuple[sqlite3.Connection,str]:
    fd,path=tempfile.mkstemp(prefix=prefix,suffix=".sqlite3")
    os.close(fd)
    try:
        connection=sqlite3.connect(path)
        connection.execute("PRAGMA journal_mode=DELETE")
        connection.execute("PRAGMA synchronous=NORMAL")
        connection.execute("PRAGMA temp_store=FILE")
        connection.execute("CREATE TABLE entries (id INTEGER PRIMARY KEY,type TEXT NOT NULL,path TEXT NOT NULL UNIQUE,mode INTEGER NOT NULL,mtime_ns INTEGER NOT NULL,size INTEGER NOT NULL DEFAULT 0,target TEXT,dev INTEGER,ino INTEGER,nlink INTEGER NOT NULL DEFAULT 1,scan_dev INTEGER,scan_ino INTEGER,scan_size INTEGER,scan_mtime_ns INTEGER,scan_mode INTEGER,canonical_path TEXT,file_number INTEGER,unstable INTEGER NOT NULL DEFAULT 0)")
        connection.execute("CREATE INDEX idx_entries_type_path ON entries(type,path)")
        connection.execute("CREATE INDEX idx_entries_inode ON entries(dev,ino)")
        connection.execute("CREATE INDEX idx_entries_canonical ON entries(canonical_path)")
        return connection,path
    except Exception:
        try:
            os.unlink(path)
        except OSError:
            pass
        raise
def scan_tree(root:str,excluded:Set[str],connection:sqlite3.Connection)->Tuple[int,int]:
    root=os.path.abspath(root)
    excluded={os.path.abspath(path) for path in excluded}
    stack:List[Tuple[str,str]]=[(root,"")]
    entry_count=0
    while stack:
        directory,prefix=stack.pop()
        try:
            children=sorted(os.scandir(directory),key=lambda entry:(entry.name.casefold(),entry.name),reverse=True)
        except OSError as exc:
            raise RuntimeError(f"Unable to read directory {directory}: {exc}") from exc
        for child in children:
            absolute=os.path.abspath(child.path)
            if absolute in excluded:
                continue
            relative=normalize_path(os.path.join(prefix,child.name) if prefix else child.name)
            validate_host_component(relative) if os.name=="nt" else None
            try:
                st=os.lstat(absolute)
            except OSError as exc:
                raise RuntimeError(f"Unable to stat {relative}: {exc}") from exc
            mode=st.st_mode
            if stat.S_ISDIR(mode):
                connection.execute("INSERT INTO entries(type,path,mode,mtime_ns,size,target,dev,ino,nlink,scan_dev,scan_ino,scan_size,scan_mtime_ns,scan_mode) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)",("dir",relative,stat.S_IMODE(mode),st.st_mtime_ns,0,None,st.st_dev,st.st_ino,st.st_nlink,st.st_dev,st.st_ino,0,st.st_mtime_ns,stat.S_IMODE(mode)))
                stack.append((absolute,relative))
            elif stat.S_ISREG(mode):
                connection.execute("INSERT INTO entries(type,path,mode,mtime_ns,size,target,dev,ino,nlink,scan_dev,scan_ino,scan_size,scan_mtime_ns,scan_mode) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)",("file",relative,stat.S_IMODE(mode),st.st_mtime_ns,st.st_size,None,st.st_dev,st.st_ino,st.st_nlink,st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,stat.S_IMODE(mode)))
            elif stat.S_ISLNK(mode):
                target=os.readlink(absolute)
                if not target or "\0" in target:
                    raise ValueError(f"Invalid symlink target: {relative}")
                connection.execute("INSERT INTO entries(type,path,mode,mtime_ns,size,target,dev,ino,nlink,scan_dev,scan_ino,scan_size,scan_mtime_ns,scan_mode) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)",("symlink",relative,stat.S_IMODE(mode),st.st_mtime_ns,0,target,st.st_dev,st.st_ino,st.st_nlink,st.st_dev,st.st_ino,0,st.st_mtime_ns,stat.S_IMODE(mode)))
            else:
                raise ValueError(f"Unsupported special filesystem object: {relative}")
            entry_count+=1
    connection.commit()
    return entry_count,0
def refresh_file_state(connection:sqlite3.Connection,root:str,strict:bool)->None:
    cursor=connection.execute("SELECT id,path,scan_dev,scan_ino,scan_size,scan_mtime_ns,scan_mode FROM entries WHERE type='file' ORDER BY path COLLATE NOCASE,path")
    while True:
        row=cursor.fetchone()
        if row is None:
            break
        row_id,path,scan_dev,scan_ino,scan_size,scan_mtime_ns,scan_mode=row
        absolute=os.path.join(root,*str(path).split("/"))
        try:
            st=os.lstat(absolute)
        except OSError as exc:
            raise RuntimeError(f"File disappeared during packing: {path}: {exc}") from exc
        if not stat.S_ISREG(st.st_mode):
            raise RuntimeError(f"File changed type during packing: {path}")
        changed=st.st_dev!=scan_dev or st.st_ino!=scan_ino or st.st_size!=scan_size or st.st_mtime_ns!=scan_mtime_ns or stat.S_IMODE(st.st_mode)!=scan_mode
        if changed and strict:
            raise RuntimeError(f"File changed during the initial scan: {path}")
        connection.execute("UPDATE entries SET dev=?,ino=?,nlink=?,size=?,mtime_ns=?,mode=?,unstable=? WHERE id=?",(st.st_dev,st.st_ino,st.st_nlink,st.st_size,st.st_mtime_ns,stat.S_IMODE(st.st_mode),1 if changed else 0,row_id))
    connection.commit()
def prepare_hardlinks(connection:sqlite3.Connection)->None:
    connection.execute("UPDATE entries SET canonical_path=NULL,file_number=NULL WHERE type='file'")
    connection.execute("UPDATE entries SET canonical_path=path WHERE type='file'")
    connection.execute("UPDATE entries SET canonical_path=(SELECT MIN(other.path) FROM entries AS other WHERE other.type='file' AND other.dev=entries.dev AND other.ino=entries.ino AND other.nlink>1) WHERE type='file' AND nlink>1")
    connection.execute("UPDATE entries SET canonical_path=path WHERE type='file' AND canonical_path IS NULL")
    connection.commit()
    assign_file_numbers(connection)
def assign_file_numbers(connection:sqlite3.Connection)->None:
    connection.execute("UPDATE entries SET file_number=NULL WHERE type='file'")
    number=0
    cursor=connection.execute("SELECT path FROM entries WHERE type='file' AND canonical_path=path ORDER BY path COLLATE NOCASE,path")
    while True:
        row=cursor.fetchone()
        if row is None:
            break
        connection.execute("UPDATE entries SET file_number=? WHERE path=?",(number,row[0]))
        number+=1
    connection.commit()
def stabilize_hardlinks(connection:sqlite3.Connection,root:str,strict:bool)->None:
    changed=False
    cursor=connection.execute("SELECT path,dev,ino FROM entries WHERE type='file' AND canonical_path<>path ORDER BY path COLLATE NOCASE,path")
    while True:
        row=cursor.fetchone()
        if row is None:
            break
        path,planned_dev,planned_ino=row
        absolute=os.path.join(root,*str(path).split("/"))
        try:
            st=os.lstat(absolute)
        except OSError as exc:
            raise RuntimeError(f"Hardlink member disappeared during packing: {path}: {exc}") from exc
        if st.st_dev!=planned_dev or st.st_ino!=planned_ino:
            if strict:
                raise RuntimeError(f"Hardlink member was replaced while packing: {path}")
            connection.execute("UPDATE entries SET canonical_path=path,dev=?,ino=?,nlink=?,size=?,mtime_ns=?,mode=?,unstable=1 WHERE path=?",(st.st_dev,st.st_ino,st.st_nlink,st.st_size,st.st_mtime_ns,stat.S_IMODE(st.st_mode),path))
            changed=True
    if changed:
        assign_file_numbers(connection)
def compare_snapshot(connection:sqlite3.Connection,root:str,excluded:Set[str])->None:
    root=os.path.abspath(root)
    excluded={os.path.abspath(path) for path in excluded}
    stored_root=connection.execute("SELECT value FROM ripdir_meta WHERE key='root_state'").fetchone()
    if stored_root is None:
        raise RuntimeError("Initial root state is missing")
    initial_root=json.loads(stored_root[0])
    try:
        root_now=os.stat(root)
    except OSError as exc:
        raise RuntimeError(f"Source root disappeared during strict packing: {root}") from exc
    current_root={"dev":int(root_now.st_dev),"ino":int(root_now.st_ino),"mode":int(stat.S_IMODE(root_now.st_mode)),"mtime_ns":int(root_now.st_mtime_ns)}
    if current_root!=initial_root:
        raise RuntimeError("Source root changed during strict packing")
    with tempfile.TemporaryDirectory(prefix="ripdir-snapshot-") as tempdir:
        snapshot_path=os.path.join(tempdir,"snapshot.sqlite3")
        final:Optional[sqlite3.Connection]=None
        try:
            final=sqlite3.connect(snapshot_path)
            final.execute("PRAGMA journal_mode=DELETE")
            final.execute("PRAGMA synchronous=NORMAL")
            final.execute("PRAGMA temp_store=FILE")
            final.execute("CREATE TABLE entries(type TEXT NOT NULL,path TEXT NOT NULL,size INTEGER NOT NULL,mode INTEGER NOT NULL,mtime_ns INTEGER NOT NULL,dev INTEGER NOT NULL,ino INTEGER NOT NULL,nlink INTEGER NOT NULL,target TEXT)")
            stack:List[Tuple[str,str]]=[(root,"")]
            while stack:
                directory,prefix=stack.pop()
                try:
                    children=sorted(os.scandir(directory),key=lambda entry:(entry.name.casefold(),entry.name),reverse=True)
                except OSError as exc:
                    raise RuntimeError(f"Unable to read directory during strict consistency check: {directory}: {exc}") from exc
                for child in children:
                    absolute=os.path.abspath(child.path)
                    if absolute in excluded:
                        continue
                    relative=normalize_path(os.path.join(prefix,child.name) if prefix else child.name)
                    try:
                        st=os.lstat(absolute)
                    except OSError as exc:
                        raise RuntimeError(f"Unable to stat path during strict consistency check: {relative}: {exc}") from exc
                    mode=st.st_mode
                    if stat.S_ISDIR(mode):
                        final.execute("INSERT INTO entries VALUES(?,?,?,?,?,?,?,?,?)",("dir",relative,0,stat.S_IMODE(mode),st.st_mtime_ns,st.st_dev,st.st_ino,st.st_nlink,None))
                        stack.append((absolute,relative))
                    elif stat.S_ISREG(mode):
                        final.execute("INSERT INTO entries VALUES(?,?,?,?,?,?,?,?,?)",("file",relative,st.st_size,stat.S_IMODE(mode),st.st_mtime_ns,st.st_dev,st.st_ino,st.st_nlink,None))
                    elif stat.S_ISLNK(mode):
                        target=os.readlink(absolute)
                        final.execute("INSERT INTO entries VALUES(?,?,?,?,?,?,?,?,?)",("symlink",relative,0,stat.S_IMODE(mode),st.st_mtime_ns,st.st_dev,st.st_ino,st.st_nlink,target))
                    else:
                        raise ValueError(f"Unsupported special filesystem object during strict consistency check: {relative}")
            final.commit()
            before=connection.execute("SELECT type,path,size,mode,mtime_ns,dev,ino,nlink,target FROM entries ORDER BY path COLLATE NOCASE,path")
            after=final.execute("SELECT type,path,size,mode,mtime_ns,dev,ino,nlink,target FROM entries ORDER BY path COLLATE NOCASE,path")
            while True:
                left=before.fetchone()
                right=after.fetchone()
                if left!=right:
                    raise RuntimeError("Source directory changed during strict packing")
                if left is None:
                    break
        finally:
            if final is not None:
                try:
                    final.close()
                except Exception:
                    pass
_GEAR_TABLE=tuple(int.from_bytes(hashlib.sha256(b"ripdir gear"+bytes([i])).digest()[:8],"big") for i in range(256))
def iter_content_chunks(source:BinaryIO)->Iterator[bytes]:
    buffer=bytearray()
    fingerprint=0
    mask=AVG_CHUNK_SIZE-1
    while True:
        block=source.read(64*1024)
        if not block:
            break
        for byte in block:
            buffer.append(byte)
            fingerprint=((fingerprint<<1)+_GEAR_TABLE[byte])&0xffffffffffffffff
            length=len(buffer)
            if length>=CHUNK_SIZE or (length>=MIN_CHUNK_SIZE and (fingerprint&mask)==0):
                yield bytes(buffer)
                buffer.clear()
                fingerprint=0
    if buffer:
        yield bytes(buffer)
def compress_payload(plaintext:bytes)->Tuple[bytes,int]:
    best=plaintext
    best_flag=0
    if zstd is not None and len(plaintext)>=1024:
        try:
            candidate=zstd.ZstdCompressor(level=3).compress(plaintext)
            if len(candidate)<len(best):
                best,best_flag=candidate,RECORD_FLAG_ZSTD
        except Exception:
            pass
    try:
        candidate=zlib.compress(plaintext,6)
        if len(candidate)<len(best):
            best,best_flag=candidate,RECORD_FLAG_ZLIB
    except Exception:
        pass
    return best,best_flag
def encrypt_record_with_key(aes:AESGCM,data_key:bytes,archive_id:bytes,file_number:int,chunk_index:int,plaintext:bytes,reference_offset:Optional[int]=None)->Tuple[bytes,bytes]:
    if reference_offset is not None:
        if reference_offset<0:
            raise ValueError("Invalid deduplication reference")
        payload=struct.pack(">Q",reference_offset)
        flags=RECORD_FLAG_REFERENCE
    else:
        payload,flags=compress_payload(plaintext)
    stored_length=len(payload)
    cipher_length=stored_length+TAG_SIZE
    record_header=RECORD_STRUCT.pack(RECORD_MAGIC,file_number,chunk_index,flags,len(plaintext),stored_length,cipher_length)
    nonce=derive_data_nonce(data_key,archive_id,file_number,chunk_index)
    ciphertext=aes.encrypt(nonce,payload,b"ripdir record"+archive_id+record_header)
    if len(ciphertext)!=cipher_length:
        raise RuntimeError("Unexpected AES-GCM ciphertext length")
    return record_header,ciphertext
class ManifestWriter:
    def __init__(self,archive:BinaryIO,manifest_key:bytes,archive_id:bytes,offset:int):
        self.archive=archive
        self.key=manifest_key
        self.archive_id=archive_id
        self.offset=offset
        self.buffer=bytearray()
        self.block_index=0
        self.bytes_written=0
        self.ciphertext_digest=hashlib.sha256()
    def add(self,entry:Dict[str,object])->None:
        line=canonical_json(entry)+b"\n"
        if len(line)>MANIFEST_BLOCK_SIZE:
            raise ValueError("Single manifest entry exceeds manifest block size")
        if self.buffer and len(self.buffer)+len(line)>MANIFEST_BLOCK_SIZE:
            self.flush()
        self.buffer.extend(line)
    def flush(self)->None:
        if not self.buffer:
            return
        plaintext=bytes(self.buffer)
        compressed=zlib.compress(plaintext,9)
        nonce=derive_manifest_nonce(self.key,self.archive_id,self.block_index)
        header=MANIFEST_BLOCK_STRUCT.pack(MANIFEST_MAGIC,self.block_index,len(plaintext),len(compressed)+TAG_SIZE)
        ciphertext=AESGCM(self.key).encrypt(nonce,compressed,b"ripdir manifest block"+self.archive_id+header)
        self.archive.write(header)
        self.archive.write(ciphertext)
        self.ciphertext_digest.update(header)
        self.ciphertext_digest.update(ciphertext)
        self.bytes_written+=len(header)+len(ciphertext)
        self.block_index+=1
        self.buffer.clear()
    def finish(self)->Tuple[int,int,int]:
        self.flush()
        return self.offset,self.bytes_written,self.block_index
class ManifestReader:
    def __init__(self,reader:"ArchiveReader",start:int,length:int,blocks:int,key:bytes,archive_id:bytes):
        self.reader=reader
        self.start=start
        self.length=length
        self.blocks=blocks
        self.key=key
        self.archive_id=archive_id
    def entries(self)->Iterator[Dict[str,object]]:
        end=self.start+self.length
        self.reader.seek(self.start)
        for index in range(self.blocks):
            header=self.reader.read(MANIFEST_BLOCK_HEADER_SIZE)
            magic,block_index,plain_len,cipher_len=MANIFEST_BLOCK_STRUCT.unpack(header)
            if magic!=MANIFEST_MAGIC or block_index!=index:
                raise ValueError("Invalid manifest block header")
            if plain_len<1 or plain_len>MANIFEST_MAX_PLAIN_BLOCK:
                raise ValueError("Invalid manifest plaintext block length")
            if cipher_len<TAG_SIZE or cipher_len>MANIFEST_MAX_CIPHER_BLOCK:
                raise ValueError("Invalid manifest ciphertext block length")
            ciphertext=self.reader.read(cipher_len)
            block_end=self.reader.tell()
            nonce=derive_manifest_nonce(self.key,self.archive_id,index)
            try:
                compressed=AESGCM(self.key).decrypt(nonce,ciphertext,b"ripdir manifest block"+self.archive_id+header)
            except Exception as exc:
                raise ValueError("Manifest authentication failed") from exc
            decompressor=zlib.decompressobj()
            plaintext=decompressor.decompress(compressed,plain_len+1)
            if len(plaintext)>plain_len or decompressor.unconsumed_tail or decompressor.unused_data or not decompressor.eof:
                raise ValueError("Malformed manifest compression")
            plaintext+=decompressor.flush()
            if len(plaintext)!=plain_len:
                raise ValueError("Manifest plaintext length mismatch")
            for line in plaintext.splitlines():
                if not line:
                    continue
                try:
                    value=json.loads(line.decode("utf-8"))
                except Exception as exc:
                    raise ValueError("Malformed manifest entry") from exc
                if not isinstance(value,dict):
                    raise ValueError("Manifest entry is not an object")
                yield value
                self.reader.seek(block_end)
            self.reader.seek(block_end)
        if self.reader.tell()!=end:
            raise ValueError("Manifest length does not match block layout")
class ArchiveReader:
    def __init__(self,file:BinaryIO,base:int,size:int):
        self.file=file
        self.base=base
        self.size=size
        self.position=0
    def seek(self,offset:int,whence:int=os.SEEK_SET)->int:
        if whence==os.SEEK_SET:
            position=offset
        elif whence==os.SEEK_CUR:
            position=self.position+offset
        elif whence==os.SEEK_END:
            position=self.size+offset
        else:
            raise ValueError("Invalid seek mode")
        if not 0<=position<=self.size:
            raise ValueError("Archive seek outside bounds")
        self.position=position
        self.file.seek(self.base+position)
        return position
    def tell(self)->int:
        return self.position
    def read(self,length:int=-1)->bytes:
        if length<0:
            length=self.size-self.position
        if length<0 or self.position+length>self.size:
            raise ValueError("Archive read outside bounds")
        data=self.file.read(length)
        if len(data)!=length:
            raise ValueError("Archive is truncated")
        self.position+=length
        return data
_RS_TABLE_CACHE=None
def _rs_tables():
    global _RS_TABLE_CACHE
    if _RS_TABLE_CACHE is not None:
        return _RS_TABLE_CACHE
    try:
        import numpy as np
    except ImportError as exc:
        raise RuntimeError("Reed-Solomon redundancy requires numpy; install it with: python -m pip install numpy") from exc
    exp=[0]*512
    log=[0]*256
    value=1
    for position in range(255):
        exp[position]=value
        log[value]=position
        value<<=1
        if value&0x100:
            value^=0x11D
    for position in range(255,512):
        exp[position]=exp[position-255]
    mul=np.zeros((256,256),dtype=np.uint8)
    for left in range(1,256):
        for right in range(1,256):
            mul[left,right]=exp[log[left]+log[right]]
    inverse=np.zeros(256,dtype=np.uint8)
    for value in range(1,256):
        inverse[value]=exp[255-log[value]]
    coefficients=[exp[index] for index in range(REDUNDANCY_DATA_SHARDS)]
    _RS_TABLE_CACHE=(np,mul,inverse,coefficients)
    return _RS_TABLE_CACHE
def _rs_parity(data_blocks:Sequence[bytes])->Tuple[bytes,bytes]:
    np,mul,inverse,coefficients=_rs_tables()
    parity_p=np.zeros(REDUNDANCY_SHARD_SIZE,dtype=np.uint8)
    parity_q=np.zeros(REDUNDANCY_SHARD_SIZE,dtype=np.uint8)
    for index,block in enumerate(data_blocks):
        array=np.frombuffer(block,dtype=np.uint8)
        np.bitwise_xor(parity_p,array,out=parity_p)
        np.bitwise_xor(parity_q,mul[coefficients[index],array],out=parity_q)
    return parity_p.tobytes(),parity_q.tobytes()
def _rs_header(logical_size:int,stripe_count:int,logical_digest:bytes,checksum_digest:bytes)->bytes:
    base=REDUNDANCY_HEADER_BASE.pack(REDUNDANCY_MAGIC,logical_size,REDUNDANCY_SHARD_SIZE,REDUNDANCY_DATA_SHARDS,REDUNDANCY_PARITY_SHARDS,stripe_count,logical_digest,checksum_digest)
    return REDUNDANCY_HEADER.pack(REDUNDANCY_MAGIC,logical_size,REDUNDANCY_SHARD_SIZE,REDUNDANCY_DATA_SHARDS,REDUNDANCY_PARITY_SHARDS,stripe_count,logical_digest,checksum_digest,zlib.crc32(base)&0xffffffff,b"\0"*4)
def _parse_rs_header(raw:bytes)->Dict[str,object]:
    if len(raw)!=REDUNDANCY_HEADER_SIZE:
        raise ValueError("Truncated redundancy header")
    magic,logical_size,shard_size,data_shards,parity_shards,stripe_count,logical_digest,checksum_digest,header_crc,reserved=REDUNDANCY_HEADER.unpack(raw)
    base=REDUNDANCY_HEADER_BASE.pack(magic,logical_size,shard_size,data_shards,parity_shards,stripe_count,logical_digest,checksum_digest)
    if magic!=REDUNDANCY_MAGIC or reserved!=b"\0"*4 or zlib.crc32(base)&0xffffffff!=header_crc:
        raise ValueError("Invalid redundancy header")
    if logical_size<HEADER_SIZE+FOOTER_SIZE or shard_size!=REDUNDANCY_SHARD_SIZE or data_shards!=REDUNDANCY_DATA_SHARDS or parity_shards!=REDUNDANCY_PARITY_SHARDS:
        raise ValueError("Unsupported redundancy parameters")
    expected_stripes=(logical_size+shard_size*data_shards-1)//(shard_size*data_shards)
    if stripe_count!=expected_stripes:
        raise ValueError("Invalid redundancy stripe count")
    return {"logical_size":logical_size,"shard_size":shard_size,"data_shards":data_shards,"parity_shards":parity_shards,"stripe_count":stripe_count,"logical_digest":logical_digest,"checksum_digest":checksum_digest}
def _read_header_copies(raw:BinaryIO)->Dict[str,object]:
    raw.seek(0)
    first=raw.read(REDUNDANCY_HEADER_SIZE)
    second=raw.read(REDUNDANCY_HEADER_SIZE)
    valid=[]
    for candidate in (first,second):
        try:
            parsed=_parse_rs_header(candidate)
            valid.append((candidate,parsed))
        except Exception:
            pass
    if not valid:
        raise ValueError("Both redundancy headers are invalid")
    if len(valid)==2 and valid[0][0]!=valid[1][0]:
        raise ValueError("Redundancy header copies disagree")
    return valid[0][1]
class RSLogicalFile:
    def __init__(self,raw:BinaryIO):
        self.raw=raw
        self.header=_read_header_copies(raw)
        self.size=int(self.header["logical_size"])
        self.position=0
        self.stripe_count=int(self.header["stripe_count"])
        self.shard_size=int(self.header["shard_size"])
        self.data_shards=int(self.header["data_shards"])
        self.parity_shards=int(self.header["parity_shards"])
        self.shard_count=self.data_shards+self.parity_shards
        self.stripe_data_bytes=self.shard_size*self.data_shards
        self.stripe_physical_bytes=self.shard_size*self.shard_count
        self.headers_size=REDUNDANCY_HEADER_SIZE*REDUNDANCY_HEADER_COPIES
        self.checksum_length=self.stripe_count*self.shard_count*REDUNDANCY_CHECKSUM_SIZE
        self.checksum_offset=self.headers_size+self.stripe_count*self.stripe_physical_bytes
        raw.seek(0,os.SEEK_END)
        physical_size=raw.tell()
        expected_size=self.checksum_offset+self.checksum_length*2
        if physical_size!=expected_size:
            raise ValueError("Redundancy container length mismatch")
        first_valid=self._checksum_table_valid(self.checksum_offset)
        second_valid=self._checksum_table_valid(self.checksum_offset+self.checksum_length)
        if first_valid:
            self.checksum_base=self.checksum_offset
        elif second_valid:
            self.checksum_base=self.checksum_offset+self.checksum_length
        else:
            raise ValueError("Both redundancy checksum tables failed authentication")
        self.corrected_shards=0
        self._cache_stripe=-1
        self._cache_data=None
        self.raw.seek(0)
    def _checksum_table_valid(self,offset:int)->bool:
        self.raw.seek(offset)
        remaining=self.checksum_length
        digest=hashlib.sha256()
        while remaining:
            block=self.raw.read(min(1024*1024,remaining))
            if not block:
                return False
            digest.update(block)
            remaining-=len(block)
        return hmac.compare_digest(digest.digest(),bytes(self.header["checksum_digest"]))
    def _checksum(self,stripe:int,shard:int)->bytes:
        offset=self.checksum_base+(stripe*self.shard_count+shard)*REDUNDANCY_CHECKSUM_SIZE
        self.raw.seek(offset)
        value=self.raw.read(REDUNDANCY_CHECKSUM_SIZE)
        if len(value)!=REDUNDANCY_CHECKSUM_SIZE:
            raise ValueError("Truncated redundancy checksum table")
        return value
    def _physical_shard(self,stripe:int,shard:int)->Optional[bytes]:
        offset=self.headers_size+stripe*self.stripe_physical_bytes+shard*self.shard_size
        try:
            self.raw.seek(offset)
            block=self.raw.read(self.shard_size)
            if len(block)!=self.shard_size:
                return None
            if not hmac.compare_digest(hashlib.sha256(block).digest(),self._checksum(stripe,shard)):
                return None
            return block
        except OSError:
            return None
    def _load_stripe(self,stripe:int)->List[bytes]:
        if stripe==self._cache_stripe and self._cache_data is not None:
            return self._cache_data
        if not 0<=stripe<self.stripe_count:
            raise ValueError("Redundancy stripe index is outside bounds")
        shards=[self._physical_shard(stripe,index) for index in range(self.shard_count)]
        missing=[index for index,block in enumerate(shards) if block is None]
        if len(missing)>self.parity_shards:
            raise ValueError(f"Unrecoverable Reed-Solomon stripe {stripe}: {len(missing)} damaged shards")
        if missing:
            np,mul,inverse,coefficients=_rs_tables()
            data=[np.frombuffer(block,dtype=np.uint8).copy() if block is not None else None for block in shards[:self.data_shards]]
            parity_p=shards[self.data_shards]
            parity_q=shards[self.data_shards+1]
            data_missing=[index for index,block in enumerate(data) if block is None]
            if len(data_missing)==1:
                missing_index=data_missing[0]
                if parity_p is not None:
                    recovered=np.frombuffer(parity_p,dtype=np.uint8).copy()
                    for index,block in enumerate(data):
                        if index!=missing_index:
                            np.bitwise_xor(recovered,block,out=recovered)
                elif parity_q is not None:
                    recovered=np.frombuffer(parity_q,dtype=np.uint8).copy()
                    for index,block in enumerate(data):
                        if index!=missing_index:
                            np.bitwise_xor(recovered,mul[coefficients[index],block],out=recovered)
                    recovered=mul[int(inverse[coefficients[missing_index]]),recovered]
                else:
                    raise ValueError(f"Reed-Solomon stripe {stripe} lacks enough parity")
                data[missing_index]=recovered
            elif len(data_missing)==2:
                if parity_p is None or parity_q is None:
                    raise ValueError(f"Reed-Solomon stripe {stripe} lacks enough parity")
                left,right=data_missing
                residual_p=np.frombuffer(parity_p,dtype=np.uint8).copy()
                residual_q=np.frombuffer(parity_q,dtype=np.uint8).copy()
                for index,block in enumerate(data):
                    if block is not None:
                        np.bitwise_xor(residual_p,block,out=residual_p)
                        np.bitwise_xor(residual_q,mul[coefficients[index],block],out=residual_q)
                coefficient_left=coefficients[left]
                coefficient_right=coefficients[right]
                denominator=coefficient_left^coefficient_right
                recovered_right=mul[int(inverse[denominator]),np.bitwise_xor(residual_q,mul[coefficient_left,residual_p])]
                recovered_left=np.bitwise_xor(residual_p,recovered_right)
                data[left]=recovered_left
                data[right]=recovered_right
            elif len(data_missing)>2:
                raise ValueError(f"Unrecoverable Reed-Solomon data stripe {stripe}")
            data_blocks=[block.tobytes() if not isinstance(block,bytes) else block for block in data]
            computed_p,computed_q=_rs_parity(data_blocks)
            rebuilt=[*data_blocks,computed_p,computed_q]
            for index in missing:
                candidate=rebuilt[index]
                if not hmac.compare_digest(hashlib.sha256(candidate).digest(),self._checksum(stripe,index)):
                    raise ValueError(f"Reed-Solomon reconstruction failed checksum for stripe {stripe}, shard {index}")
                shards[index]=candidate
            self.corrected_shards+=len(missing)
        if any(block is None for block in shards):
            raise ValueError(f"Incomplete Reed-Solomon stripe {stripe}")
        self._cache_stripe=stripe
        self._cache_data=[bytes(block) for block in shards[:self.data_shards]]
        return self._cache_data
    def seek(self,offset:int,whence:int=os.SEEK_SET)->int:
        if whence==os.SEEK_SET:
            position=offset
        elif whence==os.SEEK_CUR:
            position=self.position+offset
        elif whence==os.SEEK_END:
            position=self.size+offset
        else:
            raise ValueError("Invalid seek mode")
        if not 0<=position<=self.size:
            raise ValueError("Archive seek outside bounds")
        self.position=position
        return position
    def tell(self)->int:
        return self.position
    def read(self,length:int=-1)->bytes:
        if length<0:
            length=self.size-self.position
        if length<0 or self.position+length>self.size:
            raise ValueError("Archive read outside bounds")
        output=bytearray()
        remaining=length
        while remaining:
            stripe=self.position//self.stripe_data_bytes
            within_stripe=self.position%self.stripe_data_bytes
            data_index=within_stripe//self.shard_size
            in_shard=within_stripe%self.shard_size
            block=self._load_stripe(stripe)[data_index]
            amount=min(remaining,self.shard_size-in_shard,self.size-self.position)
            output.extend(block[in_shard:in_shard+amount])
            self.position+=amount
            remaining-=amount
        return bytes(output)
    def verify_all(self)->int:
        saved=self.position
        digest=hashlib.sha256()
        original_count=self.corrected_shards
        try:
            for stripe in range(self.stripe_count):
                blocks=self._load_stripe(stripe)
                for block_index,block in enumerate(blocks):
                    offset=stripe*self.stripe_data_bytes+block_index*self.shard_size
                    length=min(self.shard_size,max(0,self.size-offset))
                    if length:
                        digest.update(block[:length])
            if not hmac.compare_digest(digest.digest(),bytes(self.header["logical_digest"])):
                raise ValueError("Redundancy container logical digest mismatch")
            return self.corrected_shards-original_count
        finally:
            self.seek(saved)
    def close(self)->None:
        self.raw.close()
def wrap_archive_rs(path:str)->None:
    path=os.path.abspath(path)
    parent=os.path.dirname(path) or os.curdir
    with open(path,"rb") as check:
        if check.read(8)==REDUNDANCY_MAGIC:
            raise ValueError("Archive already has Reed-Solomon redundancy")
    logical_size=os.path.getsize(path)
    if logical_size<HEADER_SIZE+FOOTER_SIZE:
        raise ValueError("Cannot protect a truncated archive")
    stripe_capacity=REDUNDANCY_SHARD_SIZE*REDUNDANCY_DATA_SHARDS
    stripe_count=(logical_size+stripe_capacity-1)//stripe_capacity
    fd,temp_path=tempfile.mkstemp(prefix=".ripdir-rs-",suffix=".tmp",dir=parent)
    os.close(fd)
    checksum_temp=None
    try:
        checksum_temp=tempfile.TemporaryFile(mode="w+b")
        logical_digest=hashlib.sha256()
        checksum_digest=hashlib.sha256()
        with open(path,"rb") as source,open(temp_path,"w+b") as output:
            output.write(b"\0"*(REDUNDANCY_HEADER_SIZE*REDUNDANCY_HEADER_COPIES))
            logical_offset=0
            for stripe_index in range(stripe_count):
                data_blocks=[]
                for shard_index in range(REDUNDANCY_DATA_SHARDS):
                    remaining=max(0,logical_size-logical_offset)
                    wanted=min(REDUNDANCY_SHARD_SIZE,remaining)
                    block=bytearray()
                    while len(block)<wanted:
                        part=source.read(wanted-len(block))
                        if not part:
                            raise ValueError("Source archive changed while building redundancy")
                        block.extend(part)
                    logical_digest.update(block)
                    logical_offset+=len(block)
                    if len(block)<REDUNDANCY_SHARD_SIZE:
                        block.extend(b"\0"*(REDUNDANCY_SHARD_SIZE-len(block)))
                    data_blocks.append(bytes(block))
                parity_p,parity_q=_rs_parity(data_blocks)
                for block in (*data_blocks,parity_p,parity_q):
                    output.write(block)
                    checksum=hashlib.sha256(block).digest()
                    checksum_temp.write(checksum)
                    checksum_digest.update(checksum)
            if logical_offset!=logical_size or source.read(1):
                raise ValueError("Source archive size changed while building redundancy")
            checksum_length=stripe_count*REDUNDANCY_SHARD_COUNT*REDUNDANCY_CHECKSUM_SIZE
            checksum_temp.flush()
            checksum_temp.seek(0)
            shutil.copyfileobj(checksum_temp,output,1024*1024)
            checksum_temp.seek(0)
            shutil.copyfileobj(checksum_temp,output,1024*1024)
            expected=REDUNDANCY_HEADER_SIZE*REDUNDANCY_HEADER_COPIES+stripe_count*REDUNDANCY_SHARD_COUNT*REDUNDANCY_SHARD_SIZE+checksum_length*2
            if output.tell()!=expected:
                raise RuntimeError("Unexpected redundancy container length")
            encoded_header=_rs_header(logical_size,stripe_count,logical_digest.digest(),checksum_digest.digest())
            output.seek(0)
            output.write(encoded_header)
            output.write(encoded_header)
            output.flush()
            os.fsync(output.fileno())
        os.chmod(temp_path,stat.S_IMODE(os.stat(path).st_mode))
        os.replace(temp_path,path)
        temp_path=""
    finally:
        if checksum_temp is not None:
            checksum_temp.close()
        if temp_path:
            try:
                os.unlink(temp_path)
            except OSError:
                pass
class ArchiveContainer:
    def __init__(self,path:str):
        self.path=os.path.abspath(path)
        raw_manifest=open(self.path,"rb")
        try:
            raw_data=open(self.path,"rb")
        except Exception:
            raw_manifest.close()
            raise
        try:
            raw_manifest.seek(0,os.SEEK_END)
            physical_size=raw_manifest.tell()
            raw_manifest.seek(0)
            magic=raw_manifest.read(8)
            raw_manifest.seek(0)
            if magic==ARCHIVE_MAGIC:
                self.manifest_file=raw_manifest
                self.data_file=raw_data
                logical_size=physical_size
            elif magic==REDUNDANCY_MAGIC:
                self.manifest_file=RSLogicalFile(raw_manifest)
                self.data_file=RSLogicalFile(raw_data)
                logical_size=int(self.manifest_file.size)
                raw_manifest=None
                raw_data=None
            else:
                raise ValueError("Not a ripdir archive")
            if logical_size<HEADER_SIZE+FOOTER_SIZE:
                raise ValueError("Archive is truncated")
            self.size=logical_size
            self.manifest_reader=ArchiveReader(self.manifest_file,0,logical_size)
            self.data_reader=ArchiveReader(self.data_file,0,logical_size)
        except Exception:
            if raw_manifest is not None:
                try:
                    raw_manifest.close()
                except Exception:
                    pass
            if raw_data is not None:
                try:
                    raw_data.close()
                except Exception:
                    pass
            raise
    def verify_redundancy(self)->int:
        if isinstance(self.data_file,RSLogicalFile):
            return self.data_file.verify_all()
        return 0
    @property
    def corrected_shards(self)->int:
        return int(getattr(self.data_file,"corrected_shards",0))
    def close(self)->None:
        try:
            self.manifest_file.close()
        finally:
            self.data_file.close()
def parse_footer(reader:ArchiveReader)->Dict[str,object]:
    if reader.size<HEADER_SIZE+FOOTER_SIZE:
        raise ValueError("Archive is truncated")
    reader.seek(reader.size-FOOTER_SIZE)
    magic,manifest_offset,manifest_length,block_count,header_digest,header_mac,manifest_mac=FOOTER_STRUCT.unpack(reader.read(FOOTER_SIZE))
    if magic!=FOOTER_MAGIC:
        raise ValueError("Invalid archive footer")
    if manifest_offset<HEADER_SIZE or manifest_length<MANIFEST_BLOCK_HEADER_SIZE+TAG_SIZE or block_count<1:
        raise ValueError("Invalid manifest location")
    if manifest_offset+manifest_length!=reader.size-FOOTER_SIZE:
        raise ValueError("Manifest does not terminate at the archive footer")
    return {"manifest_offset":manifest_offset,"manifest_length":manifest_length,"block_count":block_count,"header_digest":header_digest,"header_mac":header_mac,"manifest_mac":manifest_mac}
def load_archive(container:ArchiveContainer,password:Optional[str],recipient_key_paths:Sequence[str]=())->Tuple[ManifestReader,Dict[str,object],bytes]:
    reader=container.manifest_reader
    reader.seek(0)
    header_bytes=reader.read(HEADER_SIZE)
    header=parse_header(header_bytes)
    footer=parse_footer(reader)
    envelope_length=int(header["envelope_length"])
    data_start=HEADER_SIZE+envelope_length
    if data_start>int(footer["manifest_offset"]):
        raise ValueError("Key envelope extends beyond archive content bounds")
    reader.seek(HEADER_SIZE)
    envelope_bytes=reader.read(envelope_length)
    master_key=unlock_master_key(envelope_bytes,password,bytes(header["salt"]),bytes(header["archive_id"]),recipient_key_paths)
    keys=derive_keys(master_key,bytes(header["archive_id"]))
    authenticated_header=header_bytes+envelope_bytes
    if not hmac.compare_digest(bytes(footer["header_digest"]),hashlib.sha256(authenticated_header).digest()):
        raise ValueError("Archive header integrity check failed")
    expected_mac=hmac.new(keys["header-mac"],b"ripdir authenticated header\0"+authenticated_header,hashlib.sha256).digest()
    if not hmac.compare_digest(bytes(footer["header_mac"]),expected_mac):
        raise ValueError("Archive header authentication failed")
    reader.seek(int(footer["manifest_offset"]))
    manifest_digest=hashlib.sha256()
    remaining=int(footer["manifest_length"])
    while remaining:
        block=reader.read(min(1024*1024,remaining))
        manifest_digest.update(block)
        remaining-=len(block)
    index_material=b"ripdir manifest index\0"+struct.pack(">QQI",int(footer["manifest_offset"]),int(footer["manifest_length"]),int(footer["block_count"]))+manifest_digest.digest()
    expected_manifest_mac=hmac.new(keys["index"],index_material,hashlib.sha256).digest()
    if not hmac.compare_digest(bytes(footer["manifest_mac"]),expected_manifest_mac):
        raise ValueError("Archive manifest index authentication failed")
    header["data_start"]=data_start
    header["envelope_bytes"]=envelope_bytes
    header["keys"]=keys
    manifest_reader=ManifestReader(reader,int(footer["manifest_offset"]),int(footer["manifest_length"]),int(footer["block_count"]),keys["metadata"],bytes(header["archive_id"]))
    probe=manifest_reader.entries()
    try:
        first=next(probe)
    except StopIteration as exc:
        raise ValueError("Manifest is empty") from exc
    finally:
        probe.close()
    if first.get("type")!="meta":
        raise ValueError("Invalid archive manifest")
    return manifest_reader,header,keys["payload"]
def read_manifest_meta(manifest_reader:ManifestReader)->Dict[str,object]:
    iterator=manifest_reader.entries()
    try:
        meta=next(iterator)
    except StopIteration as exc:
        raise ValueError("Manifest is empty") from exc
    if meta.get("type")!="meta" or meta.get("format")!=FORMAT:
        raise ValueError("Invalid ripdir manifest metadata")
    root_name=meta.get("root_name")
    if not isinstance(root_name,str) or not root_name:
        raise ValueError("Invalid archive root name")
    normalized=normalize_path(root_name)
    if normalized!=root_name or "/" in root_name or "\\" in root_name:
        raise ValueError("Archive root name must be a single path component")
    validate_host_component(root_name)
    for key in ("entry_count","file_count","directory_count","symlink_count","hardlink_count","content_bytes","logical_bytes","unstable_file_count"):
        try:
            if int(meta.get(key,-1))<0:
                raise ValueError
        except Exception as exc:
            raise ValueError(f"Invalid manifest metadata field: {key}") from exc
    return meta
class ManifestIndex:
    def __init__(self):
        self.tempdir=tempfile.TemporaryDirectory(prefix="ripdir-manifest-")
        self.database=os.path.join(self.tempdir.name,"manifest.sqlite3")
        self.connection:Optional[sqlite3.Connection]=None
        try:
            self.connection=sqlite3.connect(self.database)
            self.connection.execute("PRAGMA journal_mode=DELETE")
            self.connection.execute("PRAGMA synchronous=NORMAL")
            self.connection.execute("PRAGMA temp_store=FILE")
            self.connection.execute("CREATE TABLE entries(type TEXT NOT NULL,path TEXT PRIMARY KEY,mode INTEGER NOT NULL,mtime_ns INTEGER NOT NULL,size INTEGER NOT NULL,target TEXT,file_number INTEGER,offset INTEGER,chunks INTEGER,sha256 TEXT,hardlink INTEGER NOT NULL DEFAULT 0,unstable INTEGER NOT NULL DEFAULT 0)")
            self.connection.execute("CREATE INDEX idx_manifest_type ON entries(type)")
            self.connection.execute("CREATE INDEX idx_manifest_number ON entries(file_number)")
            self.connection.execute("CREATE INDEX idx_manifest_target ON entries(target)")
            if os.name=="nt":
                self.connection.execute("CREATE TABLE folded_paths(folded TEXT PRIMARY KEY,path TEXT NOT NULL)")
        except Exception:
            self.close()
            raise
    def close(self)->None:
        if self.connection is not None:
            try:
                self.connection.close()
            except Exception:
                pass
            self.connection=None
        try:
            self.tempdir.cleanup()
        except Exception:
            pass
    def execute(self,sql:str,parameters:Tuple[object,...]=()):
        if self.connection is None:
            raise RuntimeError("Manifest index is closed")
        return self.connection.execute(sql,parameters)
    def iter_dirs(self,reverse:bool=False):
        order="DESC" if reverse else "ASC"
        return self.execute(f"SELECT path,mode,mtime_ns FROM entries WHERE type='dir' ORDER BY (length(path)-length(replace(path,'/',''))) {order},path COLLATE NOCASE,path")
    def iter_canonical_files(self):
        return self.execute("SELECT path,file_number,offset,chunks,size,sha256,mode,mtime_ns,unstable FROM entries WHERE type='file' AND hardlink=0 ORDER BY file_number")
    def iter_hardlinks(self):
        return self.execute("SELECT path,target,size,mode,mtime_ns FROM entries WHERE type='file' AND hardlink=1 ORDER BY path COLLATE NOCASE,path")
    def iter_symlinks(self):
        return self.execute("SELECT path,target FROM entries WHERE type='symlink' ORDER BY path COLLATE NOCASE,path")
def validate_manifest_for_extraction(manifest_reader:ManifestReader,meta:Dict[str,object],allow_unsafe_symlinks:bool)->ManifestIndex:
    index=ManifestIndex()
    try:
        meta_seen=False
        count=0
        canonical_count=0
        directory_count=0
        symlink_count=0
        hardlink_count=0
        content_bytes=0
        logical_bytes=0
        unstable_count=0
        for entry in manifest_reader.entries():
            kind=entry.get("type")
            if kind=="meta":
                if meta_seen:
                    raise ValueError("Manifest contains multiple metadata records")
                meta_seen=True
                continue
            if kind not in {"dir","file","symlink"}:
                raise ValueError(f"Unknown manifest entry type: {kind}")
            path=normalize_path(str(entry.get("path","")))
            validate_host_component(path)
            if os.name=="nt":
                try:
                    index.execute("INSERT INTO folded_paths VALUES(?,?)",(os.path.normcase(path),path))
                except sqlite3.IntegrityError as exc:
                    raise ValueError(f"Case-insensitive archive path collision: {path}") from exc
            if kind=="dir":
                mode=int(entry.get("mode",-1))
                mtime=int(entry.get("mtime_ns",-1))
                if not 0<=mode<=0o7777 or mtime<0:
                    raise ValueError(f"Invalid directory metadata: {path}")
                index.execute("INSERT INTO entries(type,path,mode,mtime_ns,size,target,file_number,offset,chunks,sha256,hardlink,unstable) VALUES(?,?,?,?,?,?,?,?,?,?,?,?)",("dir",path,mode,mtime,0,None,None,None,None,None,0,0))
                directory_count+=1
            elif kind=="symlink":
                target=entry.get("target")
                if not isinstance(target,str) or not target or "\0" in target:
                    raise ValueError(f"Invalid symlink target: {path}")
                if not allow_unsafe_symlinks and not symlink_is_safe(path,target):
                    raise ValueError(f"Unsafe symlink target: {path} -> {target}")
                index.execute("INSERT INTO entries(type,path,mode,mtime_ns,size,target,file_number,offset,chunks,sha256,hardlink,unstable) VALUES(?,?,?,?,?,?,?,?,?,?,?,?)",("symlink",path,0,0,0,target,None,None,None,None,0,0))
                symlink_count+=1
            else:
                hardlink=bool(entry.get("hardlink",False))
                size=int(entry.get("size",-1))
                mode=int(entry.get("mode",-1))
                mtime=int(entry.get("mtime_ns",-1))
                if size<0 or mode<0 or mode>0o7777 or mtime<0:
                    raise ValueError(f"Invalid file metadata: {path}")
                if hardlink:
                    target=normalize_path(str(entry.get("target","")))
                    if target==path:
                        raise ValueError(f"Hardlink points to itself: {path}")
                    index.execute("INSERT INTO entries(type,path,mode,mtime_ns,size,target,file_number,offset,chunks,sha256,hardlink,unstable) VALUES(?,?,?,?,?,?,?,?,?,?,?,?)",("file",path,mode,mtime,size,target,None,None,None,None,1,0))
                    hardlink_count+=1
                    logical_bytes+=size
                else:
                    number=int(entry.get("file_number",-1))
                    offset=int(entry.get("offset",-1))
                    chunks=int(entry.get("chunks",-1))
                    digest=str(entry.get("sha256",""))
                    unstable=bool(entry.get("unstable",False))
                    if number<0 or offset<HEADER_SIZE or chunks<0:
                        raise ValueError(f"Invalid file content metadata: {path}")
                    if len(digest)!=64 or any(char not in "0123456789abcdef" for char in digest.lower()):
                        raise ValueError(f"Invalid SHA-256: {path}")
                    if (size==0 and chunks!=0) or (size>0 and chunks==0):
                        raise ValueError(f"Invalid chunk count for {path}")
                    index.execute("INSERT INTO entries(type,path,mode,mtime_ns,size,target,file_number,offset,chunks,sha256,hardlink,unstable) VALUES(?,?,?,?,?,?,?,?,?,?,?,?)",("file",path,mode,mtime,size,None,number,offset,chunks,digest,0,1 if unstable else 0))
                    canonical_count+=1
                    content_bytes+=size
                    logical_bytes+=size
                    if unstable:
                        unstable_count+=1
            count+=1
        if not meta_seen:
            raise ValueError("Manifest metadata record is missing")
        if count!=int(meta.get("entry_count",-1)):
            raise ValueError("Manifest entry count mismatch")
        if canonical_count!=int(meta.get("file_count",-1)):
            raise ValueError("Manifest canonical file count mismatch")
        if directory_count!=int(meta.get("directory_count",-1)):
            raise ValueError("Manifest directory count mismatch")
        if symlink_count!=int(meta.get("symlink_count",-1)):
            raise ValueError("Manifest symlink count mismatch")
        if hardlink_count!=int(meta.get("hardlink_count",-1)):
            raise ValueError("Manifest hardlink count mismatch")
        if content_bytes!=int(meta.get("content_bytes",-1)):
            raise ValueError("Manifest content byte count mismatch")
        if logical_bytes!=int(meta.get("logical_bytes",-1)):
            raise ValueError("Manifest logical byte count mismatch")
        if unstable_count!=int(meta.get("unstable_file_count",-1)):
            raise ValueError("Manifest unstable file count mismatch")
        expected_number=0
        for row in index.execute("SELECT file_number FROM entries WHERE type='file' AND hardlink=0 ORDER BY file_number"):
            if row[0] is None or int(row[0])!=expected_number:
                raise ValueError("Canonical file numbers are not contiguous")
            expected_number+=1
        for path,kind,target,hardlink,mode,mtime,size in index.execute("SELECT path,type,target,hardlink,mode,mtime_ns,size FROM entries ORDER BY path COLLATE NOCASE,path"):
            parts=path.split("/")
            for number in range(1,len(parts)):
                parent="/".join(parts[:number])
                parent_row=index.execute("SELECT type FROM entries WHERE path=?",(parent,)).fetchone()
                if parent_row is None or parent_row[0]!="dir":
                    raise ValueError(f"Archive path has a missing or non-directory ancestor: {path}")
            if kind=="file" and bool(hardlink):
                target_row=index.execute("SELECT type,hardlink,size,mode,mtime_ns FROM entries WHERE path=?",(target,)).fetchone()
                if target_row is None or target_row[0]!="file" or int(target_row[1])!=0:
                    raise ValueError(f"Hardlink target is not a canonical file: {path} -> {target}")
                if int(size)!=int(target_row[2]) or int(mode)!=int(target_row[3]) or int(mtime)!=int(target_row[4]):
                    raise ValueError(f"Hardlink metadata mismatch: {path} -> {target}")
        index.connection.commit()
        return index
    except Exception:
        index.close()
        raise
def validate_content_layout(reader:ArchiveReader,manifest_reader:ManifestReader,header:Dict[str,object])->None:
    footer=parse_footer(reader)
    payload_end=int(footer["manifest_offset"])
    cursor=int(header.get("data_start",HEADER_SIZE))
    expected_number=0
    for entry in manifest_reader.entries():
        if entry.get("type")!="file" or bool(entry.get("hardlink",False)):
            continue
        number=int(entry["file_number"])
        size=int(entry["size"])
        chunks=int(entry["chunks"])
        offset=int(entry["offset"])
        if number!=expected_number:
            raise ValueError("Canonical file numbering is invalid")
        expected_number+=1
        if offset!=cursor:
            raise ValueError(f"Archive content gap or overlap at {entry['path']}")
        if chunks==0:
            if size!=0:
                raise ValueError(f"Non-empty file has zero content records: {entry['path']}")
            continue
        reader.seek(offset)
        total_plain=0
        for chunk_index in range(chunks):
            record_start=reader.tell()
            raw=reader.read(RECORD_SIZE)
            magic,file_number,stored_chunk,flags,plain_len,stored_len,cipher_len=RECORD_STRUCT.unpack(raw)
            if magic!=RECORD_MAGIC or file_number!=number or stored_chunk!=chunk_index:
                raise ValueError(f"Invalid content record layout: {entry['path']}")
            if flags&~KNOWN_RECORD_FLAGS or flags==(RECORD_FLAG_ZLIB|RECORD_FLAG_ZSTD) or (flags&RECORD_FLAG_REFERENCE and flags!=RECORD_FLAG_REFERENCE):
                raise ValueError(f"Unknown or conflicting record flags: {entry['path']}")
            if plain_len>CHUNK_SIZE or stored_len>CHUNK_SIZE or cipher_len!=stored_len+TAG_SIZE:
                raise ValueError(f"Invalid content record lengths: {entry['path']}")
            if flags==RECORD_FLAG_REFERENCE and stored_len!=8:
                raise ValueError(f"Invalid deduplication reference record: {entry['path']}")
            if chunk_index<chunks-1 and not MIN_CHUNK_SIZE<=plain_len<=CHUNK_SIZE:
                raise ValueError(f"Non-final content-defined chunk has invalid length: {entry['path']}")
            if chunk_index==chunks-1 and not 1<=plain_len<=CHUNK_SIZE:
                raise ValueError(f"Final content-defined chunk has invalid length: {entry['path']}")
            record_end=record_start+RECORD_SIZE+cipher_len
            if record_end>payload_end:
                raise ValueError(f"Content record extends into manifest: {entry['path']}")
            total_plain+=plain_len
            reader.seek(record_end)
        if total_plain!=size:
            raise ValueError(f"Content record size mismatch: {entry['path']}")
        cursor=reader.tell()
    if cursor!=payload_end:
        raise ValueError("Archive contains unreferenced or overlapping content")
def find_entry_stream(manifest_reader:ManifestReader,path:str)->Dict[str,object]:
    normalized=normalize_path(path)
    for entry in manifest_reader.entries():
        if entry.get("type")!="meta" and entry.get("path")==normalized:
            return entry
    raise FileNotFoundError(normalized)
def resolve_hardlink(manifest_reader:ManifestReader,entry:Dict[str,object])->Dict[str,object]:
    if not bool(entry.get("hardlink",False)):
        return entry
    target=normalize_path(str(entry.get("target","")))
    for candidate in manifest_reader.entries():
        if candidate.get("type")=="file" and not bool(candidate.get("hardlink",False)) and candidate.get("path")==target:
            return candidate
    raise ValueError(f"Hardlink target missing: {entry['path']} -> {target}")
def validate_record(record_header:bytes,entry:Dict[str,object],header:Dict[str,object],expected_chunk:int)->Tuple[int,int,int,int]:
    if len(record_header)!=RECORD_SIZE:
        raise ValueError("Truncated file record")
    magic,file_number,chunk_index,flags,plain_len,stored_len,cipher_len=RECORD_STRUCT.unpack(record_header)
    if magic!=RECORD_MAGIC:
        raise ValueError("Invalid file record magic")
    if file_number!=int(entry["file_number"]) or chunk_index!=expected_chunk:
        raise ValueError("File record identity or sequence mismatch")
    if flags&~KNOWN_RECORD_FLAGS or flags==(RECORD_FLAG_ZLIB|RECORD_FLAG_ZSTD) or (flags&RECORD_FLAG_REFERENCE and flags!=RECORD_FLAG_REFERENCE):
        raise ValueError("Unknown or conflicting file record flags")
    if flags==RECORD_FLAG_REFERENCE and stored_len!=8:
        raise ValueError("Invalid deduplication reference record")
    if plain_len>int(header["chunk_size"]) or stored_len>int(header["chunk_size"]):
        raise ValueError("File record exceeds chunk size")
    if cipher_len!=stored_len+TAG_SIZE:
        raise ValueError("Invalid file ciphertext length")
    return flags,plain_len,stored_len,cipher_len
def decode_stored_chunk_at(reader:ArchiveReader,offset:int,data_key:bytes,header:Dict[str,object],expected_plain_len:int)->bytes:
    saved=reader.tell()
    try:
        footer=parse_footer(reader)
        payload_end=int(footer["manifest_offset"])
        if offset<int(header.get("data_start",HEADER_SIZE)) or offset>=saved:
            raise ValueError("Deduplication reference is outside the preceding data region")
        reader.seek(offset)
        raw=reader.read(RECORD_SIZE)
        magic,file_number,chunk_index,flags,plain_len,stored_len,cipher_len=RECORD_STRUCT.unpack(raw)
        if magic!=RECORD_MAGIC or flags==RECORD_FLAG_REFERENCE or flags&~KNOWN_RECORD_FLAGS or flags==(RECORD_FLAG_ZLIB|RECORD_FLAG_ZSTD):
            raise ValueError("Deduplication reference does not point to a stored data chunk")
        if plain_len!=expected_plain_len or cipher_len!=stored_len+TAG_SIZE or stored_len>CHUNK_SIZE or plain_len>CHUNK_SIZE:
            raise ValueError("Deduplicated chunk metadata mismatch")
        if offset+RECORD_SIZE+cipher_len>payload_end:
            raise ValueError("Deduplicated chunk extends beyond the data area")
        ciphertext=reader.read(cipher_len)
        nonce=derive_data_nonce(data_key,bytes(header["archive_id"]),file_number,chunk_index)
        try:
            payload=AESGCM(data_key).decrypt(nonce,ciphertext,b"ripdir record"+bytes(header["archive_id"])+raw)
        except Exception as exc:
            raise ValueError("Authentication failed for deduplicated chunk") from exc
        if len(payload)!=stored_len:
            raise ValueError("Stored deduplicated chunk length mismatch")
        if flags==RECORD_FLAG_ZLIB:
            decompressor=zlib.decompressobj()
            plaintext=decompressor.decompress(payload,plain_len+1)
            if len(plaintext)>plain_len or decompressor.unconsumed_tail or decompressor.unused_data or not decompressor.eof:
                raise ValueError("Malformed compressed deduplicated chunk")
            plaintext+=decompressor.flush()
        elif flags==RECORD_FLAG_ZSTD:
            if zstd is None:
                raise RuntimeError("This archive contains Zstandard-compressed chunks; install zstandard to read it")
            plaintext=zstd.ZstdDecompressor().decompress(payload,max_output_size=plain_len)
        elif flags==0:
            plaintext=payload
        else:
            raise ValueError("Invalid stored deduplicated chunk flags")
        if len(plaintext)!=expected_plain_len:
            raise ValueError("Deduplicated chunk plaintext length mismatch")
        return plaintext
    finally:
        reader.seek(saved)
def iter_plaintext_chunks(reader:ArchiveReader,entry:Dict[str,object],data_key:bytes,header:Dict[str,object],cancel_event:Optional[threading.Event]=None)->Iterator[bytes]:
    if bool(entry.get("hardlink",False)):
        raise ValueError("Hardlink entries do not contain encrypted content")
    file_number=int(entry["file_number"])
    chunk_count=int(entry["chunks"])
    expected_size=int(entry["size"])
    offset=int(entry["offset"])
    footer=parse_footer(reader)
    payload_end=int(footer["manifest_offset"])
    if offset<int(header.get("data_start",HEADER_SIZE)) or offset>payload_end:
        raise ValueError("File content offset is outside archive")
    if chunk_count==0:
        if expected_size!=0:
            raise ValueError("Non-empty file has zero chunks")
        if hashlib.sha256(b"").hexdigest()!=str(entry["sha256"]):
            raise ValueError(f"Empty file hash mismatch: {entry['path']}")
        return
    reader.seek(offset)
    aes=AESGCM(data_key)
    digest=hashlib.sha256()
    total=0
    for chunk_index in range(chunk_count):
        if cancel_event is not None and cancel_event.is_set():
            raise CancelledError("Extraction cancelled")
        record_start=reader.tell()
        raw=reader.read(RECORD_SIZE)
        flags,plain_len,stored_len,cipher_len=validate_record(raw,entry,header,chunk_index)
        if record_start+RECORD_SIZE+cipher_len>payload_end:
            raise ValueError("File record extends into manifest")
        ciphertext=reader.read(cipher_len)
        nonce=derive_data_nonce(data_key,bytes(header["archive_id"]),file_number,chunk_index)
        try:
            payload=aes.decrypt(nonce,ciphertext,b"ripdir record"+bytes(header["archive_id"])+raw)
        except Exception as exc:
            raise ValueError(f"Authentication failed for {entry['path']} chunk {chunk_index}") from exc
        if len(payload)!=stored_len:
            raise ValueError("Stored length verification failed")
        if flags==RECORD_FLAG_REFERENCE:
            if len(payload)!=8:
                raise ValueError("Malformed deduplication reference payload")
            reference_offset=struct.unpack(">Q",payload)[0]
            if reference_offset>=record_start:
                raise ValueError("Deduplication reference does not point backwards")
            plaintext=decode_stored_chunk_at(reader,reference_offset,data_key,header,plain_len)
        elif flags==RECORD_FLAG_ZLIB:
            decompressor=zlib.decompressobj()
            plaintext=decompressor.decompress(payload,plain_len+1)
            if len(plaintext)>plain_len or decompressor.unconsumed_tail or decompressor.unused_data or not decompressor.eof:
                raise ValueError("Compressed chunk is malformed or expands beyond its declaration")
            plaintext+=decompressor.flush()
        elif flags==RECORD_FLAG_ZSTD:
            if zstd is None:
                raise RuntimeError("This archive contains Zstandard-compressed chunks; install zstandard to read it")
            try:
                plaintext=zstd.ZstdDecompressor().decompress(payload,max_output_size=plain_len)
            except Exception as exc:
                raise ValueError("Zstandard chunk decompression failed") from exc
        elif flags==0:
            plaintext=payload
        else:
            raise ValueError("Invalid mutually-exclusive compression flags")
        if len(plaintext)!=plain_len:
            raise ValueError("Plaintext chunk length mismatch")
        total+=len(plaintext)
        if total>expected_size:
            raise ValueError(f"{entry['path']} exceeds declared size")
        digest.update(plaintext)
        yield plaintext
    if total!=expected_size:
        raise ValueError(f"Size mismatch for {entry['path']}")
    if not hmac.compare_digest(digest.hexdigest(),str(entry["sha256"])):
        raise ValueError(f"SHA-256 verification failed for {entry['path']}")
def safe_join(root:str,relative:str)->str:
    normalized=normalize_path(relative)
    root_abs=os.path.abspath(root)
    target=os.path.abspath(os.path.join(root_abs,*normalized.split("/")))
    try:
        if os.path.commonpath((root_abs,target))!=root_abs:
            raise ValueError
    except ValueError as exc:
        raise ValueError(f"Unsafe extraction path: {relative}") from exc
    return target
def symlink_is_safe(relative_path:str,target:str)->bool:
    if not target:
        return False
    if os.name=="nt":
        target_posix=target.replace("\\","/")
        if posixpath.isabs(target_posix) or ntpath.splitdrive(target)[0]:
            return False
    else:
        target_posix=target
        if posixpath.isabs(target_posix):
            return False
    resolved=posixpath.normpath(posixpath.join(posixpath.dirname(relative_path),target_posix))
    return resolved!=".." and not resolved.startswith("../")
def apply_file_metadata_fd(fd:int,path:str,mode:int,mtime_ns:int)->None:
    try:
        if os.chmod in getattr(os,"supports_fd",set()):
            os.chmod(fd,mode)
    except OSError:
        pass
    try:
        if os.utime in getattr(os,"supports_fd",set()):
            os.utime(fd,ns=(mtime_ns,mtime_ns))
        elif os.name=="nt":
            import ctypes
            import msvcrt
            from ctypes import wintypes
            class FILETIME(ctypes.Structure):
                _fields_=[("dwLowDateTime",wintypes.DWORD),("dwHighDateTime",wintypes.DWORD)]
            ticks=mtime_ns//100+116444736000000000
            filetime=FILETIME(ticks&0xffffffff,(ticks>>32)&0xffffffff)
            handle=wintypes.HANDLE(msvcrt.get_osfhandle(fd))
            kernel32=ctypes.WinDLL("kernel32",use_last_error=True)
            if not kernel32.SetFileTime(handle,None,ctypes.byref(filetime),ctypes.byref(filetime)):
                raise OSError(ctypes.get_last_error(),"SetFileTime failed")
    except (OSError,TypeError,ValueError,AttributeError):
        pass
def apply_directory_metadata(path:str,mode:int,mtime_ns:int)->None:
    try:
        os.chmod(path,mode)
    except OSError:
        pass
    try:
        os.utime(path,ns=(mtime_ns,mtime_ns),follow_symlinks=False)
    except OSError:
        pass
def extract_to_directory(reader:ArchiveReader,index:ManifestIndex,meta:Dict[str,object],data_key:bytes,header:Dict[str,object],destination:str,allow_unsafe_symlinks:bool,progress:Optional[ProgressCallback],cancel_event:Optional[threading.Event]=None)->None:
    os.makedirs(destination,mode=0o700,exist_ok=True)
    total_files=int(meta.get("file_count",0))
    completed_files=0
    for path,mode,mtime in index.iter_dirs(False):
        if cancel_event is not None and cancel_event.is_set():
            raise CancelledError("Extraction cancelled")
        validate_host_component(path)
        target=safe_join(destination,path)
        if os.path.lexists(target):
            raise FileExistsError(f"Path collision while creating directory: {path}")
        os.makedirs(target,mode=0o700,exist_ok=False)
    for path,number,offset,chunks,size,digest,mode,mtime,unstable in index.iter_canonical_files():
        if cancel_event is not None and cancel_event.is_set():
            raise CancelledError("Extraction cancelled")
        validate_host_component(path)
        target=safe_join(destination,path)
        parent=os.path.dirname(target)
        if not os.path.isdir(parent) or os.path.islink(parent):
            raise ValueError(f"Missing parent directory for file: {path}")
        if os.path.lexists(target):
            raise FileExistsError(f"Unexpected path collision while extracting: {path}")
        fd,temporary=tempfile.mkstemp(prefix=".ripdir-",dir=parent)
        try:
            with os.fdopen(fd,"wb",closefd=True) as output:
                fd=output.fileno()
                entry={"path":path,"file_number":int(number),"offset":int(offset),"chunks":int(chunks),"size":int(size),"sha256":digest}
                for chunk in iter_plaintext_chunks(reader,entry,data_key,header,cancel_event):
                    output.write(chunk)
                output.flush()
                os.fsync(fd)
                apply_file_metadata_fd(fd,temporary,int(mode),int(mtime))
            os.replace(temporary,target)
            temporary=""
        finally:
            if temporary:
                try:
                    os.unlink(temporary)
                except OSError:
                    pass
        completed_files+=1
        if progress:
            progress(completed_files,total_files,path)
    for path,target_path,size,mode,mtime in index.iter_hardlinks():
        if cancel_event is not None and cancel_event.is_set():
            raise CancelledError("Extraction cancelled")
        validate_host_component(path)
        validate_host_component(target_path)
        source=safe_join(destination,target_path)
        target=safe_join(destination,path)
        if not os.path.isfile(source) or os.path.islink(source):
            raise ValueError(f"Hardlink source is not a regular file: {target_path}")
        canonical=index.execute("SELECT size,mode,mtime_ns FROM entries WHERE path=? AND type='file' AND hardlink=0",(target_path,)).fetchone()
        if canonical is None:
            raise ValueError(f"Hardlink target missing: {path} -> {target_path}")
        if int(size)!=int(canonical[0]) or int(mode)!=int(canonical[1]) or int(mtime)!=int(canonical[2]):
            raise ValueError(f"Hardlink metadata mismatch: {path} -> {target_path}")
        if os.path.lexists(target):
            raise FileExistsError(f"Path collision while creating hardlink: {path}")
        try:
            os.link(source,target)
        except OSError as exc:
            raise RuntimeError(f"Unable to create hardlink {path} -> {target_path}: {exc}") from exc
        if progress:
            progress(completed_files,total_files,path)
    for path,target_value in index.iter_symlinks():
        if cancel_event is not None and cancel_event.is_set():
            raise CancelledError("Extraction cancelled")
        validate_host_component(path)
        if not allow_unsafe_symlinks and not symlink_is_safe(path,target_value):
            raise ValueError(f"Unsafe symlink target: {path} -> {target_value}")
        target=safe_join(destination,path)
        parent=os.path.dirname(target)
        if not os.path.isdir(parent) or os.path.islink(parent):
            raise ValueError(f"Missing parent directory for symlink: {path}")
        if os.path.lexists(target):
            raise FileExistsError(f"Path collision while creating symlink: {path}")
        os.symlink(target_value,target)
        if progress:
            progress(completed_files,total_files,path)
    for path,mode,mtime in index.iter_dirs(True):
        if cancel_event is not None and cancel_event.is_set():
            raise CancelledError("Extraction cancelled")
        target=safe_join(destination,path)
        apply_directory_metadata(target,int(mode),int(mtime))
    apply_directory_metadata(destination,int(meta.get("root_mode",0o755)),int(meta.get("root_mtime_ns",time.time_ns())))
def transactional_extract(container:ArchiveContainer,manifest_reader:ManifestReader,meta:Dict[str,object],data_key:bytes,header:Dict[str,object],destination:str,overwrite:bool,allow_unsafe_symlinks:bool,progress:Optional[ProgressCallback],cancel_event:Optional[threading.Event]=None)->str:
    index=validate_manifest_for_extraction(manifest_reader,meta,allow_unsafe_symlinks)
    try:
        validate_content_layout(container.data_reader,manifest_reader,header)
        destination=os.path.abspath(destination)
        parent=os.path.dirname(destination) or os.curdir
        os.makedirs(parent,exist_ok=True)
        if os.path.islink(destination):
            raise ValueError(f"Refusing to replace symlink destination: {destination}")
        if os.path.lexists(destination) and not os.path.isdir(destination):
            raise FileExistsError(f"Extraction destination is not a directory: {destination}")
        if os.path.lexists(destination) and not overwrite:
            raise FileExistsError(f"Extraction destination already exists: {destination}")
        temp_root=tempfile.mkdtemp(prefix=f".{os.path.basename(destination)}.ripdir-",dir=parent)
        try:
            try:
                os.chmod(temp_root,0o700)
            except OSError:
                pass
            extract_to_directory(container.data_reader,index,meta,data_key,header,temp_root,allow_unsafe_symlinks,progress,cancel_event)
            if cancel_event is not None and cancel_event.is_set():
                raise CancelledError("Extraction cancelled")
            if not os.path.lexists(destination):
                os.replace(temp_root,destination)
                temp_root=""
                sync_directory(parent)
                return destination
            backup=f"{destination}.ripdir-backup-{secrets.token_hex(8)}"
            try:
                os.rename(destination,backup)
            except OSError as exc:
                raise RuntimeError(f"Cannot replace existing destination. It may contain locked files or insufficient permissions: {destination}: {exc}") from exc
            try:
                os.replace(temp_root,destination)
                temp_root=""
            except Exception:
                try:
                    os.rename(backup,destination)
                except OSError as restore_exc:
                    raise RuntimeError(f"Extraction replacement failed and the original destination could not be restored. Original backup remains at {backup}: {restore_exc}")
                raise
            try:
                shutil.rmtree(backup)
            except OSError:
                print(f"{APP_NAME}: warning: previous destination retained at {backup}",file=sys.stderr)
            sync_directory(parent)
            return destination
        finally:
            if temp_root:
                shutil.rmtree(temp_root,ignore_errors=True)
    finally:
        index.close()
def sync_directory(path:str)->None:
    if os.name=="nt":
        return
    try:
        fd=os.open(path,os.O_RDONLY|getattr(os,"O_DIRECTORY",0))
    except OSError:
        return
    try:
        os.fsync(fd)
    except OSError:
        pass
    finally:
        os.close(fd)
def build_manifest_from_db(connection:sqlite3.Connection,writer:ManifestWriter,root:str,total_content:int,unstable_count:int,strict:bool)->None:
    stored_root=connection.execute("SELECT value FROM ripdir_meta WHERE key='root_state'").fetchone()
    if stored_root is None:
        raise RuntimeError("Stored root state is missing")
    root_state=json.loads(stored_root[0])
    root_name=os.path.basename(root.rstrip(os.sep)) or "root"
    logical_bytes=int(connection.execute("SELECT COALESCE(SUM(size),0) FROM entries WHERE type='file'").fetchone()[0])
    entry_count=int(connection.execute("SELECT COUNT(*) FROM entries").fetchone()[0])
    canonical_count=int(connection.execute("SELECT COUNT(*) FROM entries WHERE type='file' AND canonical_path=path").fetchone()[0])
    directory_count=int(connection.execute("SELECT COUNT(*) FROM entries WHERE type='dir'").fetchone()[0])
    symlink_count=int(connection.execute("SELECT COUNT(*) FROM entries WHERE type='symlink'").fetchone()[0])
    hardlink_count=int(connection.execute("SELECT COUNT(*) FROM entries WHERE type='file' AND canonical_path<>path").fetchone()[0])
    writer.add({"type":"meta","format":FORMAT,"root_name":root_name,"created_at":int(time.time()),"root_mode":int(root_state["mode"]),"root_mtime_ns":int(root_state["mtime_ns"]),"entry_count":entry_count,"file_count":canonical_count,"directory_count":directory_count,"symlink_count":symlink_count,"hardlink_count":hardlink_count,"content_bytes":int(total_content),"logical_bytes":logical_bytes,"unstable_file_count":int(unstable_count),"consistency":"strict" if strict else "best-effort"})
    for path,mode,mtime in connection.execute("SELECT path,mode,mtime_ns FROM entries WHERE type='dir' ORDER BY path COLLATE NOCASE,path"):
        writer.add({"type":"dir","path":path,"mode":int(mode),"mtime_ns":int(mtime)})
    for path,number,offset,chunks,size,digest,mode,mtime,unstable in connection.execute("SELECT path,file_number,offset,chunks,size,sha256,mode,mtime_ns,unstable FROM packed_files ORDER BY file_number"):
        writer.add({"type":"file","path":path,"file_number":int(number),"hardlink":False,"offset":int(offset),"chunks":int(chunks),"size":int(size),"sha256":digest,"mode":int(mode),"mtime_ns":int(mtime),"unstable":bool(unstable)})
    for path,target,size,mode,mtime in connection.execute("SELECT e.path,e.canonical_path,e.size,e.mode,e.mtime_ns FROM entries AS e WHERE e.type='file' AND e.canonical_path<>e.path ORDER BY e.path COLLATE NOCASE,e.path"):
        writer.add({"type":"file","path":path,"hardlink":True,"target":target,"size":int(size),"mode":int(mode),"mtime_ns":int(mtime)})
    for path,target in connection.execute("SELECT path,target FROM entries WHERE type='symlink' ORDER BY path COLLATE NOCASE,path"):
        writer.add({"type":"symlink","path":path,"target":target})
def build_archive(root:str,password:Optional[str],output_path:str,excluded:Set[str],strict:bool,recipient_public_paths:Sequence[str]=(),fido2_recipient:bool=False,redundancy:bool=False)->Tuple[int,int]:
    root=os.path.abspath(root)
    if not os.path.isdir(root):
        raise NotADirectoryError(root)
    connection,db_path=create_staging_db()
    connection.execute("CREATE TABLE ripdir_meta(key TEXT PRIMARY KEY,value TEXT NOT NULL)")
    try:
        root_stat=os.stat(root)
        root_state={"dev":int(root_stat.st_dev),"ino":int(root_stat.st_ino),"mode":int(stat.S_IMODE(root_stat.st_mode)),"mtime_ns":int(root_stat.st_mtime_ns)}
        connection.execute("INSERT INTO ripdir_meta(key,value) VALUES('root_state',?)",(json.dumps(root_state,separators=(",",":")),))
        entry_count,_=scan_tree(root,excluded,connection)
        refresh_file_state(connection,root,strict)
        prepare_hardlinks(connection)
        stabilize_hardlinks(connection,root,strict)
        connection.execute("CREATE TABLE packed_files(path TEXT PRIMARY KEY,file_number INTEGER NOT NULL,offset INTEGER NOT NULL,chunks INTEGER NOT NULL,size INTEGER NOT NULL,sha256 TEXT NOT NULL,mode INTEGER NOT NULL,mtime_ns INTEGER NOT NULL,unstable INTEGER NOT NULL)")
        connection.execute("CREATE TABLE chunk_dedup(digest BLOB PRIMARY KEY,offset INTEGER NOT NULL,file_number INTEGER NOT NULL,chunk_index INTEGER NOT NULL,plain_len INTEGER NOT NULL)")
        salt=secrets.token_bytes(SALT_SIZE)
        archive_id=secrets.token_bytes(ARCHIVE_ID_SIZE)
        master_key=secrets.token_bytes(KEY_SIZE)
        envelope_bytes=create_key_envelope(master_key,password,salt,archive_id,recipient_public_paths,fido2_recipient)
        header=build_header(salt,archive_id,len(envelope_bytes))
        keys=derive_keys(master_key,archive_id)
        data_key=keys["payload"]
        manifest_key=keys["metadata"]
        aes=AESGCM(data_key)
        total_content=0
        unstable_count=0
        with open(output_path,"w+b") as archive:
            archive.write(header)
            archive.write(envelope_bytes)
            canonical_rows=connection.execute("SELECT path,file_number,size,mode,mtime_ns,dev,ino,unstable FROM entries WHERE type='file' AND canonical_path=path ORDER BY file_number")
            for path,number,planned_size,planned_mode,planned_mtime,planned_dev,planned_ino,unstable in canonical_rows:
                absolute=os.path.join(root,*str(path).split("/"))
                try:
                    source=open(absolute,"rb")
                except OSError as exc:
                    raise RuntimeError(f"Unable to open file while packing: {path}: {exc}") from exc
                before=None
                after=None
                source_unstable=bool(unstable)
                has_links=False
                try:
                    before=os.fstat(source.fileno())
                    has_links=connection.execute("SELECT COUNT(*) FROM entries WHERE type='file' AND canonical_path=?",(path,)).fetchone()[0]>1
                    identity_changed=before.st_dev!=planned_dev or before.st_ino!=planned_ino
                    if identity_changed and has_links:
                        raise RuntimeError(f"Hardlink source was replaced while packing: {path}")
                    if before.st_size!=planned_size or before.st_mtime_ns!=planned_mtime or stat.S_IMODE(before.st_mode)!=planned_mode:
                        if strict:
                            raise RuntimeError(f"File changed while packing: {path}")
                        source_unstable=True
                    offset=archive.tell()
                    digest=hashlib.sha256()
                    size=0
                    chunks=0
                    for plaintext in iter_content_chunks(source):
                        digest.update(plaintext)
                        size+=len(plaintext)
                        total_content+=len(plaintext)
                        chunk_digest=hmac.new(keys["dedup"],hashlib.sha256(plaintext).digest(),hashlib.sha256).digest()
                        existing=connection.execute("SELECT offset,file_number,chunk_index,plain_len FROM chunk_dedup WHERE digest=?",(chunk_digest,)).fetchone()
                        if existing is None:
                            record_offset=archive.tell()
                            record_header,ciphertext=encrypt_record_with_key(aes,data_key,archive_id,int(number),chunks,plaintext)
                            archive.write(record_header)
                            archive.write(ciphertext)
                            connection.execute("INSERT INTO chunk_dedup VALUES(?,?,?,?,?)",(chunk_digest,record_offset,int(number),chunks,len(plaintext)))
                        else:
                            record_header,ciphertext=encrypt_record_with_key(aes,data_key,archive_id,int(number),chunks,plaintext,int(existing[0]))
                            archive.write(record_header)
                            archive.write(ciphertext)
                        chunks+=1
                    after=os.fstat(source.fileno())
                finally:
                    source.close()
                if before is None or after is None:
                    raise RuntimeError(f"Unable to determine final state: {path}")
                changed_after=after.st_dev!=before.st_dev or after.st_ino!=before.st_ino or after.st_size!=before.st_size or after.st_mtime_ns!=before.st_mtime_ns or stat.S_IMODE(after.st_mode)!=stat.S_IMODE(before.st_mode)
                source_unstable=source_unstable or changed_after
                if source_unstable and strict:
                    raise RuntimeError(f"File changed while packing: {path}")
                if after.st_ino!=before.st_ino and has_links:
                    raise RuntimeError(f"Hardlink source was replaced while packing: {path}")
                final_mode=stat.S_IMODE(after.st_mode) if source_unstable else int(planned_mode)
                final_mtime=after.st_mtime_ns if source_unstable else int(planned_mtime)
                connection.execute("INSERT INTO packed_files VALUES(?,?,?,?,?,?,?,?,?)",(path,int(number),offset,chunks,size,digest.hexdigest(),final_mode,final_mtime,1 if source_unstable else 0))
                connection.execute("UPDATE entries SET size=?,mode=?,mtime_ns=?,unstable=? WHERE type='file' AND canonical_path=?",(size,final_mode,final_mtime,1 if source_unstable else 0,path))
                if source_unstable:
                    unstable_count+=1
            connection.commit()
            if strict:
                compare_snapshot(connection,root,excluded)
            manifest_offset=archive.tell()
            writer=ManifestWriter(archive,manifest_key,archive_id,manifest_offset)
            build_manifest_from_db(connection,writer,root,total_content,unstable_count,strict)
            _,manifest_length,block_count=writer.finish()
            authenticated_header=header+envelope_bytes
            header_digest=hashlib.sha256(authenticated_header).digest()
            header_mac=hmac.new(keys["header-mac"],b"ripdir authenticated header\0"+authenticated_header,hashlib.sha256).digest()
            manifest_material=b"ripdir manifest index\0"+struct.pack(">QQI",manifest_offset,manifest_length,block_count)+writer.ciphertext_digest.digest()
            manifest_mac=hmac.new(keys["index"],manifest_material,hashlib.sha256).digest()
            footer=FOOTER_STRUCT.pack(FOOTER_MAGIC,manifest_offset,manifest_length,block_count,header_digest,header_mac,manifest_mac)
            archive.write(footer)
            archive.flush()
            os.fsync(archive.fileno())
        if redundancy:
            wrap_archive_rs(output_path)
        return entry_count,total_content
    finally:
        try:
            connection.close()
        finally:
            try:
                os.unlink(db_path)
            except OSError:
                pass
def zip_payload_path()->Optional[str]:
    global _ZIP_PAYLOAD_TEMP
    if _ZIP_PAYLOAD_TEMP:
        existing=os.path.join(_ZIP_PAYLOAD_TEMP,PAYLOAD_NAME)
        if os.path.isfile(existing):
            return existing
        _ZIP_PAYLOAD_TEMP=None
    candidate=os.path.abspath(sys.argv[0]) if sys.argv and sys.argv[0] else ""
    if not candidate or not zipfile.is_zipfile(candidate):
        return None
    try:
        with zipfile.ZipFile(candidate,"r") as archive:
            info=archive.getinfo(PAYLOAD_NAME)
            tempdir=tempfile.mkdtemp(prefix="ripdir-payload-")
            target=os.path.join(tempdir,PAYLOAD_NAME)
            with archive.open(info,"r") as source,open(target,"wb") as destination:
                shutil.copyfileobj(source,destination,1024*1024)
            _ZIP_PAYLOAD_TEMP=tempdir
            return target
    except (KeyError,zipfile.BadZipFile,OSError):
        return None
def cleanup_zip_payload()->None:
    global _ZIP_PAYLOAD_TEMP
    if _ZIP_PAYLOAD_TEMP:
        shutil.rmtree(_ZIP_PAYLOAD_TEMP,ignore_errors=True)
        _ZIP_PAYLOAD_TEMP=None
atexit.register(cleanup_zip_payload)
def payload_candidate_paths()->Iterator[str]:
    candidates=[]
    try:
        candidates.append(os.path.join(os.path.dirname(os.path.abspath(__file__)),PAYLOAD_NAME))
    except Exception:
        pass
    if sys.argv and sys.argv[0]:
        try:
            candidates.append(os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])),PAYLOAD_NAME))
        except Exception:
            pass
    try:
        compiled_dir=getattr(__compiled__,"containing_dir",None)
    except NameError:
        compiled_dir=None
    if compiled_dir:
        candidates.append(os.path.join(os.path.abspath(str(compiled_dir)),PAYLOAD_NAME))
    seen:Set[str]=set()
    for candidate in candidates:
        normalized=os.path.abspath(candidate)
        if normalized not in seen:
            seen.add(normalized)
            yield normalized
def has_embedded_payload()->bool:
    for candidate in payload_candidate_paths():
        if os.path.isfile(candidate):
            return True
    return zip_payload_path() is not None
def embedded_payload_path()->str:
    for candidate in payload_candidate_paths():
        if os.path.isfile(candidate):
            return candidate
    extracted=zip_payload_path()
    if extracted is not None:
        return extracted
    raise FileNotFoundError(PAYLOAD_NAME)
def filesystem_source_path()->str:
    source=os.path.abspath(__file__)
    if not os.path.isfile(source):
        raise RuntimeError("Nuitka self-extractor builds require a filesystem-backed Python source file")
    return source
def build_nuitka_command(source_path:str,payload_path:str,workdir:str,output_name:str,console_mode:bool)->List[str]:
    command=[sys.executable,"-m","nuitka","--mode=onefile","--follow-imports","--enable-plugin=tk-inter","--python-flag=-B","--python-flag=no_docstrings","--python-flag=no_asserts",f"--include-data-files={payload_path}={PAYLOAD_NAME}",f"--output-dir={workdir}",f"--output-filename={output_name}",source_path]
    if os.name=="nt":
        command.append("--windows-console-mode=force" if console_mode else "--windows-console-mode=attach")
    return command
def build_raw(root:str,output:str,password:Optional[str],force:bool,strict:bool,recipient_public_paths:Sequence[str]=(),fido2_recipient:bool=False,redundancy:bool=False)->None:
    output=os.path.abspath(output)
    if os.path.exists(output) and not force:
        raise FileExistsError(f"Output exists: {output}. Use --force to replace it.")
    parent=os.path.dirname(output) or os.curdir
    os.makedirs(parent,exist_ok=True)
    fd,temp=tempfile.mkstemp(prefix=".ripdir-",suffix=".tmp",dir=parent)
    os.close(fd)
    try:
        entries,content=build_archive(root,password,temp,{output,temp},strict,recipient_public_paths,fido2_recipient,redundancy)
        os.replace(temp,output)
        temp=""
        print(f"Created ripdir archive: {output}")
        print(f"Entries: {entries}")
        print(f"Content bytes: {content:,}")
        print(f"Archive bytes: {os.path.getsize(output):,}")
    finally:
        if temp:
            try:
                os.unlink(temp)
            except OSError:
                pass
def load_release_private_key(path:str)->Ed25519PrivateKey:
    with open(path,"rb") as source:
        encoded=source.read()
    try:
        key=serialization.load_pem_private_key(encoded,password=None)
    except (TypeError,ValueError):
        password=getpass.getpass("Release signing-key password: ")
        key=serialization.load_pem_private_key(encoded,password=password.encode("utf-8"))
    if not isinstance(key,Ed25519PrivateKey):
        raise ValueError("Release signing key must be an Ed25519 private key")
    return key
def generate_release_key(path:str)->None:
    path=os.path.abspath(path)
    parent=os.path.dirname(path) or os.curdir
    os.makedirs(parent,exist_ok=True)
    if os.path.exists(path):
        raise FileExistsError(f"Signing key already exists: {path}")
    password=get_password(confirm=True,prefer_gui=True)
    if password is None:
        return
    key=Ed25519PrivateKey.generate()
    encoded=key.private_bytes(serialization.Encoding.PEM,serialization.PrivateFormat.PKCS8,serialization.BestAvailableEncryption(password.encode("utf-8")))
    flags=os.O_WRONLY|os.O_CREAT|os.O_EXCL
    fd=os.open(path,flags,0o600)
    try:
        with os.fdopen(fd,"wb") as output:
            output.write(encoded)
            output.flush()
            os.fsync(output.fileno())
    except Exception:
        try:
            os.unlink(path)
        except OSError:
            pass
        raise
    public=key.public_key().public_bytes(serialization.Encoding.Raw,serialization.PublicFormat.Raw)
    print(f"Created encrypted Ed25519 release key: {path}")
    print(f"Public key: {public.hex()}")
    print("Keep the private key outside the application repository and do not distribute it with the executable.")
def generate_recipient_key(prefix:str,key_type:str="x25519")->None:
    prefix=os.path.abspath(prefix)
    parent=os.path.dirname(prefix) or os.curdir
    os.makedirs(parent,exist_ok=True)
    private_path=prefix+".private.pem"
    public_path=prefix+".public.pem"
    if os.path.exists(private_path) or os.path.exists(public_path):
        raise FileExistsError("Recipient key output already exists")
    password=get_password(confirm=True,prefer_gui=True)
    if password is None:
        return
    if key_type=="x25519":
        private=x25519.X25519PrivateKey.generate()
    elif key_type=="rsa":
        private=rsa.generate_private_key(public_exponent=65537,key_size=3072)
    else:
        raise ValueError("Recipient key type must be x25519 or rsa")
    private_bytes=private.private_bytes(serialization.Encoding.PEM,serialization.PrivateFormat.PKCS8,serialization.BestAvailableEncryption(password.encode("utf-8")))
    public_bytes=private.public_key().public_bytes(serialization.Encoding.PEM,serialization.PublicFormat.SubjectPublicKeyInfo)
    created=[]
    try:
        for path,data,mode in ((private_path,private_bytes,0o600),(public_path,public_bytes,0o644)):
            fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL,mode)
            created.append(path)
            with os.fdopen(fd,"wb") as output:
                output.write(data)
                output.flush()
                os.fsync(output.fileno())
    except Exception:
        for path in created:
            try:
                os.unlink(path)
            except OSError:
                pass
        raise
    print(f"Recipient private key: {private_path}")
    print(f"Recipient public key: {public_path}")
    print("Keep the encrypted private key and its password separate from the archive.")
def machine_binding_id()->str:
    value=None
    system=platform.system()
    if system=="Linux":
        for candidate in ("/etc/machine-id","/var/lib/dbus/machine-id"):
            try:
                text=Path(candidate).read_text(encoding="utf-8").strip()
                if text:
                    value=text
                    break
            except OSError:
                pass
    elif system=="Windows":
        try:
            import winreg
            with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE,r"SOFTWARE\Microsoft\Cryptography") as key:
                value=winreg.QueryValueEx(key,"MachineGuid")[0]
        except Exception:
            value=None
    elif system=="Darwin":
        try:
            result=subprocess.run(["ioreg","-rd1","-c","IOPlatformExpertDevice"],capture_output=True,text=True,timeout=3,check=True)
            for line in result.stdout.splitlines():
                if "IOPlatformUUID" in line:
                    value=line.split("=",1)[1].strip().strip('"')
                    break
        except Exception:
            value=None
    if not value:
        raise RuntimeError("Cannot obtain a stable host identifier on this operating system")
    material=("ripdir host binding\0"+system+"\0"+str(value)).encode("utf-8")
    return hashlib.sha256(material).hexdigest()
def debugger_detected()->bool:
    try:
        if sys.gettrace() is not None or sys.getprofile() is not None:
            return True
    except Exception:
        pass
    if os.name=="nt":
        try:
            import ctypes
            if ctypes.windll.kernel32.IsDebuggerPresent():
                return True
        except Exception:
            pass
    elif sys.platform.startswith("linux"):
        try:
            with open("/proc/self/status","r",encoding="ascii",errors="ignore") as source:
                for line in source:
                    if line.startswith("TracerPid:"):
                        return int(line.split(":",1)[1].strip())!=0
        except Exception:
            pass
    return False
def file_sha256(path:str,limit:Optional[int]=None)->bytes:
    digest=hashlib.sha256()
    remaining=limit
    with open(path,"rb") as source:
        while True:
            if remaining is not None and remaining<=0:
                break
            chunk=source.read(1024*1024 if remaining is None else min(1024*1024,remaining))
            if not chunk:
                if remaining is not None and remaining>0:
                    raise ValueError("Signed executable is truncated")
                break
            digest.update(chunk)
            if remaining is not None:
                remaining-=len(chunk)
    return digest.digest()
def is_compiled_runtime()->bool:
    return bool(getattr(sys,"frozen",False)) or "__compiled__" in globals()
def verify_release_integrity()->Optional[str]:
    public_hex=TRUSTED_RELEASE_PUBLIC_KEY_HEX
    if not public_hex:
        if is_compiled_runtime():
            raise RuntimeError("Unsigned or unpinned ripdir executable; rebuild it with --release-signing-key")
        return None
    try:
        public=Ed25519PublicKey.from_public_bytes(bytes.fromhex(public_hex))
    except Exception as exc:
        raise RuntimeError("Embedded release verification key is invalid") from exc
    executable=os.path.abspath(sys.argv[0]) if sys.argv and sys.argv[0] else ""
    if not executable or not os.path.isfile(executable):
        raise RuntimeError("Cannot locate the executable for runtime integrity verification")
    signature_path=executable+SIGNATURE_SIDECAR_SUFFIX
    try:
        with open(signature_path,"rb") as source:
            signature=source.read(SIGNATURE_SIZE+1)
        if len(signature)!=SIGNATURE_SIZE:
            raise ValueError("Detached release signature is missing or malformed")
        digest=file_sha256(executable)
        public.verify(signature,RELEASE_SIGNATURE_CONTEXT+digest)
    except Exception as exc:
        raise RuntimeError(f"Executable integrity verification failed: {exc}") from exc
    return digest.hex()
class HTTPSOnlyRedirectHandler(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,request,response,code,message,headers,new_url):
        if urllib.parse.urlparse(new_url).scheme.lower()!="https":
            raise urllib.error.HTTPError(new_url,code,"Refusing a non-HTTPS license redirect",headers,response)
        return super().redirect_request(request,response,code,message,headers,new_url)
def check_remote_lease(binary_digest:Optional[str])->None:
    if not LICENSE_ENDPOINT:
        return
    if not TRUSTED_LICENSE_PUBLIC_KEY_HEX:
        raise RuntimeError("Remote authorization is configured without a pinned license-server public key")
    parsed=urllib.parse.urlparse(LICENSE_ENDPOINT)
    if parsed.scheme.lower()!="https" or not parsed.netloc:
        raise RuntimeError("The license endpoint must use HTTPS")
    if not binary_digest:
        raise RuntimeError("Remote authorization requires a signed executable build")
    try:
        public=Ed25519PublicKey.from_public_bytes(bytes.fromhex(TRUSTED_LICENSE_PUBLIC_KEY_HEX))
    except Exception as exc:
        raise RuntimeError("Embedded license-server verification key is invalid") from exc
    device_id=machine_binding_id()
    challenge=secrets.token_hex(24)
    request_body=canonical_json({"product":APP_NAME,"binary_sha256":binary_digest,"device_id":device_id,"challenge":challenge,"timestamp":int(time.time())})
    request=urllib.request.Request(LICENSE_ENDPOINT,data=request_body,headers={"Content-Type":"application/json","Accept":"application/json","User-Agent":"ripdir"},method="POST")
    try:
        opener=urllib.request.build_opener(HTTPSOnlyRedirectHandler())
        with opener.open(request,timeout=8) as response:
            if response.status!=200:
                raise RuntimeError(f"License server returned HTTP {response.status}")
            response_bytes=response.read(65537)
            if len(response_bytes)>65536:
                raise RuntimeError("License server response exceeds the size limit")
        envelope=json.loads(response_bytes.decode("utf-8"))
        payload=envelope["payload"]
        signature=base64.b64decode(envelope["signature"],validate=True)
        if not isinstance(payload,dict):
            raise ValueError("Lease payload is not an object")
        public.verify(signature,LICENSE_SIGNATURE_CONTEXT+canonical_json(payload))
        expires=int(payload.get("expires_at",0))
        if payload.get("product")!=APP_NAME or payload.get("allowed") is not True:
            raise RuntimeError("License server denied this execution")
        if payload.get("binary_sha256")!=binary_digest or payload.get("device_id")!=device_id or payload.get("challenge")!=challenge:
            raise RuntimeError("License lease does not match this executable or device")
        now=int(time.time())
        if expires<now or expires>now+30*24*60*60:
            raise RuntimeError("License lease is expired or has an invalid lifetime")
        global _ACTIVE_LEASE
        _ACTIVE_LEASE=envelope
    except RuntimeError:
        raise
    except Exception as exc:
        raise RuntimeError(f"Remote authorization failed: {exc}") from exc
def harden_process()->None:
    # Best-effort native mitigations. These raise the cost of casual memory
    # inspection; they are not a substitute for keeping secrets server-side.
    if os.name=="nt":
        try:
            import ctypes
            ctypes.windll.kernel32.SetDefaultDllDirectories(0x00001000)
        except Exception:
            pass
        try:
            import ctypes
            ctypes.windll.kernel32.SetErrorMode(0x0001|0x0002|0x8000)
        except Exception:
            pass
        return
    try:
        import resource
        resource.setrlimit(resource.RLIMIT_CORE,(0,0))
    except Exception:
        pass
    if sys.platform.startswith("linux"):
        try:
            import ctypes
            libc=ctypes.CDLL(None,use_errno=True)
            # Linux PR_SET_DUMPABLE=4; prevent ordinary core dumps and ptrace
            # attachment by other processes while the protected runtime runs.
            if libc.prctl(4,0,0,0,0)!=0:
                pass
        except Exception:
            pass
def runtime_integrity_watchdog(executable:str,expected_digest:Optional[str])->None:
    if not expected_digest:
        return
    public=Ed25519PublicKey.from_public_bytes(bytes.fromhex(TRUSTED_RELEASE_PUBLIC_KEY_HEX))
    while True:
        time.sleep(20)
        try:
            actual=file_sha256(executable).hex()
            with open(executable+SIGNATURE_SIDECAR_SUFFIX,"rb") as source:
                signature=source.read(SIGNATURE_SIZE+1)
            if len(signature)!=SIGNATURE_SIZE:
                raise ValueError("Detached signature is missing or malformed")
            public.verify(signature,RELEASE_SIGNATURE_CONTEXT+bytes.fromhex(actual))
            if not hmac.compare_digest(actual,expected_digest):
                os._exit(126)
            if RUNTIME_ANTI_DEBUG and debugger_detected():
                os._exit(126)
            if LICENSE_ENDPOINT:
                lease=_ACTIVE_LEASE
                payload=lease.get("payload",{}) if isinstance(lease,dict) else {}
                expiry=int(payload.get("expires_at",0)) if isinstance(payload,dict) else 0
                if expiry<=int(time.time())+60:
                    check_remote_lease(expected_digest)
        except BaseException:
            os._exit(126)
def enforce_runtime_protection()->None:
    digest=verify_release_integrity()
    enrollment_query=bool(sys.argv[1:]) and sys.argv[1:]==["--device-id"]
    if enrollment_query:
        return
    if is_compiled_runtime() and TRUSTED_RELEASE_PUBLIC_KEY_HEX:
        harden_process()
    if TRUSTED_MACHINE_BINDING_HEX:
        actual=machine_binding_id()
        if not hmac.compare_digest(actual,TRUSTED_MACHINE_BINDING_HEX):
            raise RuntimeError("This ripdir executable is bound to a different host")
    if RUNTIME_ANTI_DEBUG and debugger_detected():
        raise RuntimeError("Runtime debugging or tracing was detected")
    check_remote_lease(digest)
    if digest and is_compiled_runtime():
        executable=os.path.abspath(sys.argv[0])
        worker=threading.Thread(target=runtime_integrity_watchdog,args=(executable,digest),name="ripdir-integrity-watchdog",daemon=True)
        worker.start()
def private_key_public_hex(key:Ed25519PrivateKey)->str:
    return key.public_key().public_bytes(serialization.Encoding.Raw,serialization.PublicFormat.Raw).hex()
def release_signature_bytes(path:str,key:Ed25519PrivateKey)->bytes:
    digest=file_sha256(path)
    return key.sign(RELEASE_SIGNATURE_CONTEXT+digest)
def write_signature_sidecar(executable_path:str,signature_path:str,key:Ed25519PrivateKey)->None:
    signature=release_signature_bytes(executable_path,key)
    with open(signature_path,"wb") as output:
        output.write(signature)
        output.flush()
        os.fsync(output.fileno())
NATIVE_STUB_TEMPLATE = r"""
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <openssl/evp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#ifndef RIPDIR_PUBLIC_KEY_HEX
#define RIPDIR_PUBLIC_KEY_HEX ""
#endif
static const unsigned char signature_context[] = "ripdir release integrity";
static const unsigned char trailer_magic[8] = {'R','I','P','N','A','T','I','V'};
static void fail(const char *message) { dprintf(STDERR_FILENO, "ripdir launcher: %s\n", message); }
static int hex_value(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}
static int decode_public_key(unsigned char out[32]) {
    const char *hex = RIPDIR_PUBLIC_KEY_HEX;
    if (strlen(hex) != 64) return -1;
    for (size_t i = 0; i < 32; ++i) {
        int hi = hex_value(hex[i * 2]), lo = hex_value(hex[i * 2 + 1]);
        if (hi < 0 || lo < 0) return -1;
        out[i] = (unsigned char)((hi << 4) | lo);
    }
    return 0;
}
static int pread_exact(int fd, void *buffer, size_t length, off_t offset) {
    unsigned char *p = (unsigned char *)buffer;
    size_t done = 0;
    while (done < length) {
        ssize_t n = pread(fd, p + done, length - done, offset + (off_t)done);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) return -1;
        done += (size_t)n;
    }
    return 0;
}
static int write_exact(int fd, const void *buffer, size_t length) {
    const unsigned char *p = (const unsigned char *)buffer;
    size_t done = 0;
    while (done < length) {
        ssize_t n = write(fd, p + done, length - done);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) return -1;
        done += (size_t)n;
    }
    return 0;
}
static int sha256_region(int fd, off_t offset, uint64_t length, unsigned char digest[32]) {
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    unsigned char buffer[1024 * 1024];
    unsigned int digest_length = 0;
    if (!ctx) return -1;
    if (EVP_DigestInit_ex(ctx, EVP_sha256(), NULL) != 1) { EVP_MD_CTX_free(ctx); return -1; }
    uint64_t remaining = length;
    off_t position = offset;
    while (remaining) {
        size_t amount = remaining < sizeof(buffer) ? (size_t)remaining : sizeof(buffer);
        if (pread_exact(fd, buffer, amount, position) != 0 || EVP_DigestUpdate(ctx, buffer, amount) != 1) {
            EVP_MD_CTX_free(ctx); return -1;
        }
        remaining -= amount;
        position += (off_t)amount;
    }
    int ok = EVP_DigestFinal_ex(ctx, digest, &digest_length) == 1 && digest_length == 32;
    EVP_MD_CTX_free(ctx);
    return ok ? 0 : -1;
}
static int verify_ed25519(const unsigned char pub[32], const unsigned char signature[64], const unsigned char digest[32]) {
    EVP_PKEY *key = EVP_PKEY_new_raw_public_key(EVP_PKEY_ED25519, NULL, pub, 32);
    EVP_MD_CTX *ctx = NULL;
    unsigned char message[sizeof(signature_context) + 32];
    memcpy(message, signature_context, sizeof(signature_context));
    memcpy(message + sizeof(signature_context), digest, 32);
    int ok = 0;
    if (!key) return -1;
    ctx = EVP_MD_CTX_new();
    if (ctx && EVP_DigestVerifyInit(ctx, NULL, NULL, NULL, key) == 1 && EVP_DigestVerify(ctx, signature, 64, message, sizeof(message)) == 1) ok = 1;
    if (ctx) EVP_MD_CTX_free(ctx);
    EVP_PKEY_free(key);
    return ok ? 0 : -1;
}
static int read_detached_signature(const char *path, unsigned char signature[64]) {
    int fd = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return -1;
    struct stat st;
    int ok = fstat(fd, &st) == 0 && S_ISREG(st.st_mode) && st.st_size == 64 && pread_exact(fd, signature, 64, 0) == 0;
    close(fd);
    return ok ? 0 : -1;
}
static int copy_region_to_file(int source_fd, off_t offset, uint64_t length, int output_fd) {
    unsigned char buffer[1024 * 1024];
    uint64_t remaining = length;
    off_t position = offset;
    while (remaining) {
        size_t amount = remaining < sizeof(buffer) ? (size_t)remaining : sizeof(buffer);
        if (pread_exact(source_fd, buffer, amount, position) != 0 || write_exact(output_fd, buffer, amount) != 0) return -1;
        remaining -= amount;
        position += (off_t)amount;
    }
    return 0;
}
static uint64_t read_be64(const unsigned char b[8]) {
    uint64_t value = 0;
    for (size_t i = 0; i < 8; ++i) value = (value << 8) | b[i];
    return value;
}
static void remove_temp(const char *payload, const char *signature, const char *directory) {
    if (signature && *signature) unlink(signature);
    if (payload && *payload) unlink(payload);
    if (directory && *directory) rmdir(directory);
}
int main(int argc, char **argv) {
    int self_fd = -1, payload_fd = -1, sig_fd = -1;
    char self_path[PATH_MAX] = {0}, sidecar_path[PATH_MAX] = {0}, temp_dir[] = "/tmp/ripdir-run-XXXXXX";
    char payload_path[PATH_MAX] = {0}, payload_sig_path[PATH_MAX] = {0};
    unsigned char public_key[32], wrapper_signature[64], payload_signature[64], trailer[16], wrapper_digest[32], payload_digest[32], copied_digest[32];
    struct stat self_stat;
    int temp_created = 0, result = 126;
    if (decode_public_key(public_key) != 0) { fail("invalid pinned release key"); goto cleanup; }
    self_fd = open("/proc/self/exe", O_RDONLY | O_CLOEXEC);
    if (self_fd < 0 || fstat(self_fd, &self_stat) != 0 || !S_ISREG(self_stat.st_mode) || self_stat.st_size < 80) { fail("cannot open executable image"); goto cleanup; }
    ssize_t path_length = readlink("/proc/self/exe", self_path, sizeof(self_path) - 1);
    if (path_length <= 0 || (size_t)path_length >= sizeof(self_path) - 1) { fail("cannot resolve executable path"); goto cleanup; }
    self_path[path_length] = '\0';
    if (strstr(self_path, " (deleted)") != NULL) { fail("executable was deleted while running"); goto cleanup; }
    if (snprintf(sidecar_path, sizeof(sidecar_path), "%s.sig", self_path) >= (int)sizeof(sidecar_path)) { fail("signature path is too long"); goto cleanup; }
    if (read_detached_signature(sidecar_path, wrapper_signature) != 0) { fail("release signature is missing or malformed"); goto cleanup; }
    if (sha256_region(self_fd, 0, (uint64_t)self_stat.st_size, wrapper_digest) != 0 || verify_ed25519(public_key, wrapper_signature, wrapper_digest) != 0) { fail("executable signature verification failed"); goto cleanup; }
    if (pread_exact(self_fd, trailer, sizeof(trailer), self_stat.st_size - (off_t)sizeof(trailer)) != 0 || memcmp(trailer, trailer_magic, sizeof(trailer_magic)) != 0) { fail("native payload trailer is missing"); goto cleanup; }
    uint64_t payload_size = read_be64(trailer + 8);
    off_t payload_signature_offset = self_stat.st_size - (off_t)sizeof(trailer) - 64;
    if (payload_size == 0 || payload_size > (uint64_t)payload_signature_offset) { fail("invalid native payload bounds"); goto cleanup; }
    off_t payload_offset = payload_signature_offset - (off_t)payload_size;
    if (payload_offset <= 0) { fail("invalid native payload offset"); goto cleanup; }
    if (pread_exact(self_fd, payload_signature, sizeof(payload_signature), payload_signature_offset) != 0) { fail("cannot read native payload signature"); goto cleanup; }
    if (sha256_region(self_fd, payload_offset, payload_size, payload_digest) != 0 || verify_ed25519(public_key, payload_signature, payload_digest) != 0) { fail("embedded payload signature verification failed"); goto cleanup; }
    if (!mkdtemp(temp_dir)) { fail("cannot create private runtime directory"); goto cleanup; }
    temp_created = 1;
    if (snprintf(payload_path, sizeof(payload_path), "%s/payload", temp_dir) >= (int)sizeof(payload_path) || snprintf(payload_sig_path, sizeof(payload_sig_path), "%s/payload.sig", temp_dir) >= (int)sizeof(payload_sig_path)) { fail("runtime path too long"); goto cleanup; }
    payload_fd = open(payload_path, O_CREAT | O_EXCL | O_WRONLY | O_CLOEXEC | O_NOFOLLOW, 0700);
    if (payload_fd < 0) { fail("cannot create private payload file"); goto cleanup; }
    if (copy_region_to_file(self_fd, payload_offset, payload_size, payload_fd) != 0 || fchmod(payload_fd, 0700) != 0 || fsync(payload_fd) != 0) { fail("cannot extract verified payload"); goto cleanup; }
    if (close(payload_fd) != 0) { payload_fd = -1; fail("cannot close extracted payload"); goto cleanup; }
    payload_fd = -1;
    payload_fd = open(payload_path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (payload_fd < 0) { fail("cannot reopen extracted payload for final verification"); goto cleanup; }
    struct stat payload_stat;
    if (fstat(payload_fd, &payload_stat) != 0 || !S_ISREG(payload_stat.st_mode) || (uint64_t)payload_stat.st_size != payload_size || sha256_region(payload_fd, 0, payload_size, copied_digest) != 0 || verify_ed25519(public_key, payload_signature, copied_digest) != 0) { fail("extracted payload failed final verification"); goto cleanup; }
    close(payload_fd);
    payload_fd = -1;
    sig_fd = open(payload_sig_path, O_CREAT | O_EXCL | O_WRONLY | O_CLOEXEC | O_NOFOLLOW, 0600);
    if (sig_fd < 0 || write_exact(sig_fd, payload_signature, sizeof(payload_signature)) != 0 || fsync(sig_fd) != 0) { fail("cannot create payload signature file"); goto cleanup; }
    if (close(sig_fd) != 0) { sig_fd = -1; fail("cannot close payload signature file"); goto cleanup; }
    sig_fd = -1;
    char **child_argv = calloc((size_t)argc + 1, sizeof(char *));
    if (!child_argv) { fail("out of memory preparing process arguments"); goto cleanup; }
    child_argv[0] = payload_path;
    for (int i = 1; i < argc; ++i) child_argv[i] = argv[i];
    pid_t child = fork();
    if (child < 0) { free(child_argv); fail("cannot start protected runtime"); goto cleanup; }
    if (child == 0) {
        execv(payload_path, child_argv);
        dprintf(STDERR_FILENO, "ripdir launcher: cannot execute protected runtime: %s\n", strerror(errno));
        _exit(127);
    }
    free(child_argv);
    int status = 0;
    while (waitpid(child, &status, 0) < 0) {
        if (errno == EINTR) continue;
        fail("failed waiting for protected runtime");
        goto cleanup;
    }
    if (WIFEXITED(status)) result = WEXITSTATUS(status);
    else if (WIFSIGNALED(status)) result = 128 + WTERMSIG(status);
    else result = 126;
cleanup:
    if (payload_fd >= 0) close(payload_fd);
    if (sig_fd >= 0) close(sig_fd);
    if (self_fd >= 0) close(self_fd);
    if (temp_created) remove_temp(payload_path, payload_sig_path, temp_dir);
    return result;
}
"""
def make_protected_build_source(source_path:str,destination:str,public_hex:str,machine_binding:str,anti_debug:bool,license_endpoint:str,license_public_key_hex:str,backend_endpoint:str)->None:
    text=Path(source_path).read_text(encoding="utf-8")
    replacements=(
        (r'^TRUSTED_RELEASE_PUBLIC_KEY_HEX=""$',f'TRUSTED_RELEASE_PUBLIC_KEY_HEX={json.dumps(public_hex)}'),
        (r'^TRUSTED_MACHINE_BINDING_HEX=""$',f'TRUSTED_MACHINE_BINDING_HEX={json.dumps(machine_binding)}'),
        (r'^RUNTIME_ANTI_DEBUG=False$',f'RUNTIME_ANTI_DEBUG={bool(anti_debug)!r}'),
        (r'^LICENSE_ENDPOINT=""$',f'LICENSE_ENDPOINT={json.dumps(license_endpoint)}'),
        (r'^TRUSTED_LICENSE_PUBLIC_KEY_HEX=""$',f'TRUSTED_LICENSE_PUBLIC_KEY_HEX={json.dumps(license_public_key_hex)}'),
        (r'^BACKEND_ENDPOINT=""$',f'BACKEND_ENDPOINT={json.dumps(backend_endpoint)}')
    )
    for pattern,replacement in replacements:
        text,count=re.subn(pattern,replacement,text,count=1,flags=re.MULTILINE)
        if count!=1:
            raise RuntimeError(f"Cannot safely inject release protection setting: {pattern}")
    Path(destination).write_text(text,encoding="utf-8")
def compile_native_launcher(public_hex:str,workdir:str)->Tuple[Optional[str],str]:
    compiler=shutil.which("cc")
    if not compiler or not sys.platform.startswith("linux"):
        return None,"not available on this platform"
    source_path=os.path.join(workdir,"ripdir_native_launcher.c")
    executable_path=os.path.join(workdir,"ripdir-native-launcher")
    source=NATIVE_STUB_TEMPLATE.replace('#define RIPDIR_PUBLIC_KEY_HEX ""',f'#define RIPDIR_PUBLIC_KEY_HEX "{public_hex}"')
    with open(source_path,"w",encoding="utf-8") as output:
        output.write(source)
    common=[compiler,"-std=c11","-Os","-ffunction-sections","-fdata-sections","-s","-D_FORTIFY_SOURCE=2","-fstack-protector-strong","-Wall","-Wextra","-Werror",source_path,"-o",executable_path]
    static_command=common+["-static","-Wl,--gc-sections","-lcrypto","-lz","-lzstd","-ldl","-pthread","-lm"]
    try:
        subprocess.run(static_command,check=True,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE,text=True)
        return executable_path,"static"
    except (subprocess.CalledProcessError,OSError):
        try:
            subprocess.run(common+["-lcrypto"],check=True,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE,text=True)
            return executable_path,"dynamic OpenSSL"
        except (subprocess.CalledProcessError,OSError):
            return None,"C compiler or OpenSSL development libraries were unavailable"
def build_native_linux_wrapper(stub_path:str,payload_path:str,output_path:str,signing_key:Ed25519PrivateKey)->None:
    payload_size=os.path.getsize(payload_path)
    if payload_size<=0:
        raise ValueError("Compiled payload is empty")
    payload_signature=release_signature_bytes(payload_path,signing_key)
    with open(output_path,"wb") as output:
        with open(stub_path,"rb") as stub:
            shutil.copyfileobj(stub,output,1024*1024)
        with open(payload_path,"rb") as payload:
            shutil.copyfileobj(payload,output,1024*1024)
        output.write(payload_signature)
        output.write(NATIVE_TRAILER_STRUCT.pack(NATIVE_TRAILER_MAGIC,payload_size))
        output.flush()
        os.fsync(output.fileno())
    os.chmod(output_path,0o755)

def build_self_extracting(root:str,output:str,password:Optional[str],force:bool,strict:bool,console_mode:bool,release_signing_key:str,bind_host:bool,anti_debug:bool,license_endpoint:str,license_public_key_hex:str,recipient_public_paths:Sequence[str]=(),backend_endpoint:str="",fido2_recipient:bool=False,redundancy:bool=False)->None:
    output=os.path.abspath(output)
    if os.path.exists(output) and not force:
        raise FileExistsError(f"Output exists: {output}. Use --force to replace it.")
    source_path=filesystem_source_path()
    if output==source_path:
        raise ValueError("Output cannot overwrite the ripdir builder source")
    if not release_signing_key:
        raise ValueError("Self-extracting executables require --release-signing-key")
    if bool(license_endpoint)!=bool(license_public_key_hex):
        raise ValueError("--license-endpoint and --license-public-key must be supplied together")
    if backend_endpoint and not license_endpoint:
        raise ValueError("--backend-endpoint requires remote licensing via --license-endpoint")
    for label,url in (("license",license_endpoint),("backend",backend_endpoint)):
        parsed=urllib.parse.urlparse(url) if url else None
        if url and (parsed.scheme.lower()!="https" or not parsed.netloc):
            raise ValueError(f"The {label} endpoint must be an absolute HTTPS URL")
    if license_public_key_hex:
        key_bytes=bytes.fromhex(license_public_key_hex)
        if len(key_bytes)!=32:
            raise ValueError("--license-public-key must be a 32-byte Ed25519 public key encoded as 64 hexadecimal characters")
        license_public_key_hex=key_bytes.hex()
    private_key=load_release_private_key(release_signing_key)
    public_hex=private_key_public_hex(private_key)
    binding=machine_binding_id() if bind_host else ""
    parent=os.path.dirname(output) or os.curdir
    os.makedirs(parent,exist_ok=True)
    fd,archive_temp=tempfile.mkstemp(prefix=".ripdir-build-",suffix=".ripdir",dir=parent)
    os.close(fd)
    try:
        entries,content=build_archive(root,password,archive_temp,{output,archive_temp},strict,recipient_public_paths,fido2_recipient,redundancy)
        try:
            subprocess.run([sys.executable,"-m","nuitka","--version"],check=True,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
        except Exception as exc:
            raise RuntimeError("Nuitka is required for self-extracting archives. Install it with: python3 -m pip install Nuitka") from exc
        native_mode="Nuitka only"
        with tempfile.TemporaryDirectory(prefix="ripdir-nuitka-") as workdir:
            build_source=os.path.join(workdir,"ripdir_protected_build.py")
            make_protected_build_source(source_path,build_source,public_hex,binding,anti_debug,license_endpoint,license_public_key_hex,backend_endpoint)
            command=build_nuitka_command(build_source,archive_temp,workdir,os.path.basename(output),console_mode)
            subprocess.run(command,check=True)
            compiled=os.path.join(workdir,os.path.basename(output))
            if not os.path.isfile(compiled):
                raise RuntimeError("Nuitka did not produce the requested executable")
            if os.name!="nt":
                strip=shutil.which("strip")
                if strip:
                    subprocess.run([strip,"--strip-unneeded",compiled],check=False,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
            fd2,temp_output=tempfile.mkstemp(prefix=".ripdir-exe-",suffix=".tmp",dir=parent)
            os.close(fd2)
            fd3,temp_signature=tempfile.mkstemp(prefix=".ripdir-signature-",suffix=".tmp",dir=parent)
            os.close(fd3)
            try:
                if sys.platform.startswith("linux") and os.name!="nt":
                    stub_path,mode=compile_native_launcher(public_hex,workdir)
                    if stub_path:
                        build_native_linux_wrapper(stub_path,compiled,temp_output,private_key)
                        native_mode=f"Linux native launcher ({mode})"
                    else:
                        shutil.copyfile(compiled,temp_output)
                        if os.name!="nt":
                            os.chmod(temp_output,os.stat(compiled).st_mode|stat.S_IXUSR|stat.S_IXGRP|stat.S_IXOTH)
                        print(f"{APP_NAME}: warning: native launcher skipped: {mode}",file=sys.stderr)
                else:
                    shutil.copyfile(compiled,temp_output)
                    if os.name!="nt":
                        os.chmod(temp_output,os.stat(compiled).st_mode|stat.S_IXUSR|stat.S_IXGRP|stat.S_IXOTH)
                write_signature_sidecar(temp_output,temp_signature,private_key)
                os.replace(temp_output,output)
                temp_output=""
                os.replace(temp_signature,output+SIGNATURE_SIDECAR_SUFFIX)
                temp_signature=""
            finally:
                for leftover in (temp_output,temp_signature):
                    if leftover:
                        try:
                            os.unlink(leftover)
                        except OSError:
                            pass
        print(f"Created signed self-extracting ripdir archive: {output}")
        print(f"Entries: {entries}")
        print(f"Content bytes: {content:,}")
        print(f"Executable bytes: {os.path.getsize(output):,}")
        print(f"Executable SHA-256: {file_sha256(output).hex()}")
        print(f"Release signature: Ed25519 detached signature at {output+SIGNATURE_SIDECAR_SUFFIX}")
        print(f"Startup verification: {native_mode}")
        if bind_host:
            print("Host binding: enabled; this executable is bound to the build host OS installation identifier")
        if anti_debug:
            print("Runtime debugger checks: enabled (best effort)")
        if license_endpoint:
            print(f"Remote lease endpoint: {license_endpoint}")
        if backend_endpoint:
            print(f"Server-side backend endpoint: {backend_endpoint}")
    finally:
        try:
            os.unlink(archive_temp)
        except OSError:
            pass
def archive_path_from_args(args)->Optional[str]:
    if args.archive:
        return os.path.abspath(args.archive)
    try:
        return embedded_payload_path()
    except FileNotFoundError:
        return None
def verify_archive(path:str,password:Optional[str],progress:Optional[ProgressCallback]=None,recipient_keys:Sequence[str]=())->Tuple[int,int]:
    container=ArchiveContainer(path)
    try:
        repaired=container.verify_redundancy()
        if repaired:
            print(f"Reconstructed {repaired} damaged redundancy shards in memory",file=sys.stderr)
        manifest_reader,header,data_key=load_archive(container,password,recipient_keys)
        meta=read_manifest_meta(manifest_reader)
        index=validate_manifest_for_extraction(manifest_reader,meta,True)
        try:
            validate_content_layout(container.data_reader,manifest_reader,header)
            count=0
            total=0
            for path,number,offset,chunks,size,digest,mode,mtime,unstable in index.iter_canonical_files():
                entry={"path":path,"file_number":int(number),"offset":int(offset),"chunks":int(chunks),"size":int(size),"sha256":digest}
                for chunk in iter_plaintext_chunks(container.data_reader,entry,data_key,header):
                    total+=len(chunk)
                count+=1
                if progress:
                    progress(count,int(meta["file_count"]),str(path))
            return count,total
        finally:
            index.close()
    finally:
        container.close()
def repair_archive(path:str,password:Optional[str],output_path:str,recipient_keys:Sequence[str]=())->Tuple[int,int]:
    source_path=os.path.abspath(path)
    output_path=os.path.abspath(output_path)
    parent=os.path.dirname(output_path) or os.curdir
    os.makedirs(parent,exist_ok=True)
    container=ArchiveContainer(source_path)
    temp_path=""
    try:
        if not isinstance(container.data_file,RSLogicalFile):
            raise ValueError("--repair requires an archive created with --redundancy")
        repaired_before=container.verify_redundancy()
        verified_files,verified_bytes=verify_archive(source_path,password,recipient_keys=recipient_keys)
        fd,temp_path=tempfile.mkstemp(prefix=".ripdir-repair-",suffix=".tmp",dir=parent)
        os.close(fd)
        reader=container.data_reader
        saved=reader.tell()
        try:
            reader.seek(0)
            with open(temp_path,"wb") as destination:
                remaining=reader.size
                digest=hashlib.sha256()
                while remaining:
                    block=reader.read(min(1024*1024,remaining))
                    destination.write(block)
                    digest.update(block)
                    remaining-=len(block)
                destination.flush()
                os.fsync(destination.fileno())
            if not hmac.compare_digest(digest.digest(),bytes(container.data_file.header["logical_digest"])):
                raise ValueError("Reconstructed archive failed its outer logical digest")
        finally:
            reader.seek(saved)
    finally:
        container.close()
    try:
        wrap_archive_rs(temp_path)
        if os.path.exists(output_path) and os.path.samefile(temp_path,output_path):
            raise ValueError("Repair staging path unexpectedly matches output")
        os.replace(temp_path,output_path)
        temp_path=""
        sync_directory(parent)
        print(f"Rebuilt redundancy-protected archive: {output_path}")
        print(f"Verified canonical files: {verified_files}")
        print(f"Verified plaintext bytes: {verified_bytes:,}")
        print(f"Recovered shard count on initial pass: {repaired_before}")
        return verified_files,verified_bytes
    finally:
        if temp_path:
            try:
                os.unlink(temp_path)
            except OSError:
                pass
def list_archive(path:str,password:Optional[str],recipient_keys:Sequence[str]=())->None:
    container=ArchiveContainer(path)
    try:
        manifest_reader,header,data_key=load_archive(container,password,recipient_keys)
        meta=read_manifest_meta(manifest_reader)
        index=validate_manifest_for_extraction(manifest_reader,meta,True)
        try:
            validate_content_layout(container.data_reader,manifest_reader,header)
            print(f"Format: {meta['format']}")
            print(f"Root: {meta['root_name']}")
            print(f"Created: {time.ctime(int(meta['created_at']))}")
            print(f"Files: {meta['file_count']}")
            print(f"Directories: {meta['directory_count']}")
            print(f"Symlinks: {meta['symlink_count']}")
            print(f"Hardlinks: {meta['hardlink_count']}")
            print(f"Content bytes: {int(meta['content_bytes']):,}")
            print(f"Logical bytes: {int(meta['logical_bytes']):,}")
            print(f"Consistency: {meta['consistency']}")
            print(f"Unstable files: {meta['unstable_file_count']}")
            for path,mode,mtime in index.iter_dirs(False):
                print(f"D {path}/")
            for path,number,offset,chunks,size,digest,mode,mtime,unstable in index.iter_canonical_files():
                marker=" unstable" if bool(unstable) else ""
                print(f"F {path}  {size} bytes  sha256={digest}{marker}")
            for path,target,size,mode,mtime in index.iter_hardlinks():
                print(f"H {path} -> {target}")
            for path,target in index.iter_symlinks():
                print(f"S {path} -> {target}")
        finally:
            index.close()
    finally:
        container.close()
def cat_archive(path:str,password:Optional[str],requested_path:str,recipient_keys:Sequence[str]=())->None:
    container=ArchiveContainer(path)
    try:
        manifest_reader,header,data_key=load_archive(container,password,recipient_keys)
        meta=read_manifest_meta(manifest_reader)
        index=validate_manifest_for_extraction(manifest_reader,meta,True)
        try:
            validate_content_layout(container.data_reader,manifest_reader,header)
            entry=find_entry_stream(manifest_reader,requested_path)
            if entry.get("type")!="file":
                raise ValueError("--cat requires a regular file")
            if bool(entry.get("hardlink",False)):
                entry=resolve_hardlink(manifest_reader,entry)
            for chunk in iter_plaintext_chunks(container.data_reader,entry,data_key,header):
                sys.stdout.buffer.write(chunk)
            sys.stdout.buffer.flush()
        finally:
            index.close()
    finally:
        container.close()
def console_extract(path:str,password_stdin:bool=False,overwrite:bool=False,allow_unsafe_symlinks:bool=False,recipient_keys:Sequence[str]=())->int:
    password=None if recipient_keys else get_password(stdin=password_stdin)
    if password is None:
        return 0
    container=ArchiveContainer(path)
    try:
        manifest_reader,header,data_key=load_archive(container,password,recipient_keys)
        meta=read_manifest_meta(manifest_reader)
        index=validate_manifest_for_extraction(manifest_reader,meta,allow_unsafe_symlinks)
        try:
            validate_content_layout(container.data_reader,manifest_reader,header)
        finally:
            index.close()
        parent=input("Choose where to restore the archive: ").strip()
        if not parent:
            return 0
        destination=os.path.join(os.path.abspath(parent),str(meta["root_name"]))
        if os.path.lexists(destination) and not overwrite:
            answer=input(f"'{meta['root_name']}' already exists. Replace it? [y/N]: ").strip().lower()
            if answer not in {"y","yes"}:
                return 0
            overwrite=True
        restored=transactional_extract(container,manifest_reader,meta,data_key,header,destination,overwrite,allow_unsafe_symlinks,lambda done,total,name: print(f"Extracted {done:,}/{total:,}: {name}",file=sys.stderr))
        print(f"Extracted to: {restored}")
        return 0
    finally:
        container.close()
def gui_extract(path:str,password_stdin:bool=False,recipient_keys:Sequence[str]=())->int:
    try:
        import tkinter as tk
        from tkinter import filedialog,messagebox,ttk
    except Exception:
        return console_extract(path,password_stdin=password_stdin,recipient_keys=recipient_keys)
    try:
        root=tk.Tk()
    except Exception:
        return console_extract(path,password_stdin=password_stdin,recipient_keys=recipient_keys)
    root.withdraw()
    try:
        try:
            password=None if recipient_keys else get_password(prefer_gui=not password_stdin,stdin=password_stdin)
        except GuiUnavailable:
            return console_extract(path,password_stdin=password_stdin,recipient_keys=recipient_keys)
        if password is None:
            return 0
        container=ArchiveContainer(path)
        try:
            try:
                manifest_reader,header,data_key=load_archive(container,password,recipient_keys)
                meta=read_manifest_meta(manifest_reader)
                index=validate_manifest_for_extraction(manifest_reader,meta,False)
                try:
                    validate_content_layout(container.data_reader,manifest_reader,header)
                finally:
                    index.close()
            except Exception as exc:
                messagebox.showerror(APP_NAME,str(exc),parent=root)
                return 1
            parent=filedialog.askdirectory(title="Choose where to restore the archive",parent=root)
            if not parent:
                return 0
            destination=os.path.join(os.path.abspath(parent),str(meta["root_name"]))
            overwrite=False
            if os.path.lexists(destination):
                overwrite=messagebox.askyesno(APP_NAME,f"'{meta['root_name']}' already exists. Replace it?",parent=root)
                if not overwrite:
                    return 0
            window=tk.Toplevel(root)
            window.title(APP_NAME)
            window.geometry("640x190")
            window.resizable(False,False)
            window.protocol("WM_DELETE_WINDOW",lambda:None)
            status_label=ttk.Label(window,text="Preparing extraction...")
            status_label.pack(fill="x",padx=16,pady=(20,8))
            progress_bar=ttk.Progressbar(window,orient="horizontal",mode="determinate",maximum=max(1,int(meta["file_count"])))
            progress_bar.pack(fill="x",padx=16,pady=8)
            detail_label=ttk.Label(window,text="")
            detail_label.pack(fill="x",padx=16,pady=4)
            cancel_button=ttk.Button(window,text="Cancel")
            cancel_button.pack(pady=8)
            messages:queue.Queue=queue.Queue()
            cancel_event=threading.Event()
            result:Dict[str,object]={"ok":False,"error":None}
            def progress(done:int,total:int,name:str)->None:
                messages.put(("progress",done,total,name))
            def cancel()->None:
                cancel_event.set()
                cancel_button.configure(state="disabled")
                status_label.configure(text="Cancelling...")
            cancel_button.configure(command=cancel)
            def worker()->None:
                try:
                    messages.put(("status","Extracting archive..."))
                    transactional_extract(container,manifest_reader,meta,data_key,header,destination,overwrite,False,progress,cancel_event)
                    messages.put(("done",))
                except Exception as exc:
                    messages.put(("error",str(exc)))
            thread=threading.Thread(target=worker,name="ripdir-extract",daemon=True)
            thread.start()
            def pump()->None:
                try:
                    while True:
                        message=messages.get_nowait()
                        if message[0]=="progress":
                            _,done,total,name=message
                            progress_bar.configure(value=done,maximum=max(1,total))
                            status_label.configure(text=f"Extracting {done:,} / {total:,} files")
                            detail_label.configure(text=str(name))
                        elif message[0]=="status":
                            status_label.configure(text=str(message[1]))
                        elif message[0]=="done":
                            result["ok"]=True
                        elif message[0]=="error":
                            result["error"]=message[1]
                except queue.Empty:
                    pass
                if thread.is_alive():
                    root.after(50,pump)
                    return
                try:
                    window.destroy()
                except Exception:
                    pass
                if bool(result["ok"]):
                    messagebox.showinfo(APP_NAME,f"Extraction complete.\n\n{destination}",parent=root)
                elif str(result.get("error"))=="Extraction cancelled":
                    messagebox.showinfo(APP_NAME,"Extraction cancelled. No destination changes were committed.",parent=root)
                else:
                    messagebox.showerror(APP_NAME,str(result["error"]),parent=root)
                root.destroy()
            root.after(50,pump)
            root.deiconify()
            root.mainloop()
            return 0 if bool(result["ok"]) else 1
        finally:
            container.close()
    finally:
        try:
            root.destroy()
        except Exception:
            pass
def remote_backend_call(endpoint:str,operation:str,payload:object,timeout:float=20.0)->object:
    if _ACTIVE_LEASE is None:
        raise RuntimeError("No verified remote authorization lease is active")
    parsed=urllib.parse.urlparse(endpoint)
    if parsed.scheme.lower()!="https" or not parsed.netloc:
        raise ValueError("Remote backend endpoints must use HTTPS")
    if not operation or len(operation)>128 or any(char not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._-" for char in operation):
        raise ValueError("Invalid backend operation name")
    try:
        canonical_json(payload)
    except Exception as exc:
        raise ValueError("Backend payload must be JSON-serializable") from exc
    request_id=secrets.token_hex(16)
    request_body=canonical_json({"lease":_ACTIVE_LEASE,"operation":operation,"payload":payload,"request_id":request_id})
    if len(request_body)>65536:
        raise ValueError("Backend request exceeds 64 KiB")
    request=urllib.request.Request(endpoint,data=request_body,headers={"Content-Type":"application/json","Accept":"application/json","Cache-Control":"no-store","User-Agent":"ripdir"},method="POST")
    opener=urllib.request.build_opener(HTTPSOnlyRedirectHandler())
    try:
        with opener.open(request,timeout=timeout) as response:
            if response.status!=200:
                raise RuntimeError(f"Backend returned HTTP {response.status}")
            encoded=response.read(1024*1024+1)
        if len(encoded)>1024*1024:
            raise RuntimeError("Backend response exceeds 1 MiB")
        envelope=json.loads(encoded.decode("utf-8"))
        response_payload=envelope["payload"]
        signature=base64.b64decode(envelope["signature"],validate=True)
        public=Ed25519PublicKey.from_public_bytes(bytes.fromhex(TRUSTED_LICENSE_PUBLIC_KEY_HEX))
        public.verify(signature,LICENSE_SIGNATURE_CONTEXT+canonical_json(response_payload))
        lease_payload=_ACTIVE_LEASE["payload"]
        if response_payload.get("product")!=APP_NAME or response_payload.get("allowed") is not True:
            raise RuntimeError("Backend denied the operation")
        if response_payload.get("operation")!=operation or response_payload.get("request_id")!=request_id:
            raise RuntimeError("Backend response does not match the request")
        if response_payload.get("device_id")!=lease_payload.get("device_id") or response_payload.get("binary_sha256")!=lease_payload.get("binary_sha256"):
            raise RuntimeError("Backend response is bound to a different client")
        if int(response_payload.get("expires_at",0))<int(time.time()):
            raise RuntimeError("Backend response expired")
        return response_payload.get("result")
    except urllib.error.URLError as exc:
        raise RuntimeError(f"Remote backend request failed: {exc}") from exc
    except Exception as exc:
        if isinstance(exc,RuntimeError):
            raise
        raise RuntimeError(f"Invalid or unauthenticated backend response: {exc}") from exc
def mount_archive(path:str,password:Optional[str],mountpoint:str,recipient_keys:Sequence[str]=())->int:
    try:
        from fuse import FUSE,Operations,FuseOSError
    except Exception as exc:
        raise RuntimeError("Read-only mounting requires fusepy and a working FUSE implementation") from exc
    if os.name=="nt":
        raise RuntimeError("The built-in FUSE mount frontend is supported on Linux and macOS only")
    mountpoint=os.path.abspath(mountpoint)
    if not os.path.isdir(mountpoint):
        raise NotADirectoryError(f"Mount point must be an existing directory: {mountpoint}")
    container=ArchiveContainer(path)
    index=None
    try:
        manifest_reader,header,data_key=load_archive(container,password,recipient_keys)
        meta=read_manifest_meta(manifest_reader)
        index=validate_manifest_for_extraction(manifest_reader,meta,False)
        validate_content_layout(container.data_reader,manifest_reader,header)
        class ReadOnlyRipdirFS(Operations):
            def _relative(self,path:str)->str:
                value=path.lstrip("/")
                return normalize_path(value) if value else ""
            def _row(self,path:str):
                relative=self._relative(path)
                if not relative:
                    return ("dir",int(meta.get("root_mode",0o755)),int(meta.get("root_mtime_ns",0)),0,None,None,None,None,None,0)
                return index.execute("SELECT type,mode,mtime_ns,size,target,file_number,offset,chunks,sha256,hardlink FROM entries WHERE path=?",(relative,)).fetchone()
            def getattr(self,path:str,fh=None):
                row=self._row(path)
                if row is None:
                    raise FuseOSError(2)
                kind,mode,mtime,size,target,number,offset,chunks,digest,hardlink=row
                if kind=="dir":
                    file_mode=stat.S_IFDIR|int(mode)
                    size_value=0
                    nlink=2
                elif kind=="symlink":
                    file_mode=stat.S_IFLNK|0o777
                    size_value=len(str(target).encode("utf-8"))
                    nlink=1
                else:
                    file_mode=stat.S_IFREG|int(mode)
                    size_value=int(size)
                    nlink=1
                now=float(mtime)/1_000_000_000 if mtime else 0.0
                return {"st_mode":file_mode,"st_nlink":nlink,"st_size":size_value,"st_ctime":now,"st_mtime":now,"st_atime":now,"st_uid":os.getuid(),"st_gid":os.getgid(),"st_ino":int.from_bytes(hashlib.sha256(self._relative(path).encode("utf-8")).digest()[:8],"big")}
            def readdir(self,path:str,fh):
                relative=self._relative(path)
                yield "."
                yield ".."
                if not relative:
                    cursor=index.execute("SELECT path FROM entries WHERE instr(path,'/')=0 ORDER BY path COLLATE NOCASE,path")
                else:
                    prefix=relative+"/"
                    cursor=index.execute("SELECT path FROM entries WHERE substr(path,1,?)=? AND instr(substr(path,?),'/')=0 ORDER BY path COLLATE NOCASE,path",(len(prefix),prefix,len(prefix)+1))
                for row in cursor:
                    candidate=str(row[0])
                    name=candidate if not relative else candidate[len(relative)+1:]
                    if name and "/" not in name:
                        yield name
            def readlink(self,path:str):
                row=self._row(path)
                if row is None or row[0]!="symlink":
                    raise FuseOSError(22)
                return str(row[4])
            def open(self,path:str,flags:int):
                if flags&(os.O_WRONLY|os.O_RDWR|os.O_APPEND|os.O_TRUNC):
                    raise FuseOSError(30)
                row=self._row(path)
                if row is None or row[0]!="file":
                    raise FuseOSError(2)
                return 0
            def read(self,path:str,size:int,offset:int,fh):
                row=self._row(path)
                if row is None or row[0]!="file":
                    raise FuseOSError(2)
                file_path=self._relative(path)
                kind,mode,mtime,length,target,number,record_offset,chunks,digest,hardlink=row
                if offset<0 or size<0:
                    raise FuseOSError(22)
                if offset>=int(length) or size==0:
                    return b""
                if bool(hardlink):
                    canonical=index.execute("SELECT path,file_number,offset,chunks,size,sha256 FROM entries WHERE path=? AND type='file' AND hardlink=0",(target,)).fetchone()
                    if canonical is None:
                        raise FuseOSError(5)
                    file_path,number,record_offset,chunks,length,digest=canonical
                else:
                    file_path=file_path
                file_entry={"path":file_path,"file_number":int(number),"offset":int(record_offset),"chunks":int(chunks),"size":int(length),"sha256":str(digest)}
                requested_end=min(int(length),offset+size)
                logical_offset=0
                pieces=[]
                for chunk in iter_plaintext_chunks(container.data_reader,file_entry,data_key,header):
                    chunk_end=logical_offset+len(chunk)
                    if chunk_end>offset and logical_offset<requested_end:
                        left=max(0,offset-logical_offset)
                        right=min(len(chunk),requested_end-logical_offset)
                        pieces.append(chunk[left:right])
                    logical_offset=chunk_end
                    if logical_offset>=requested_end:
                        break
                return b"".join(pieces)
        FUSE(ReadOnlyRipdirFS(),mountpoint,foreground=True,ro=True,nothreads=True)
        return 0
    finally:
        if index is not None:
            index.close()
        container.close()
def run_license_server(bind_address:str,signing_key_path:str,policy_path:str,backend_module_path:Optional[str]=None)->None:
    if ":" not in bind_address:
        raise ValueError("Bind address must be HOST:PORT")
    host,port_text=bind_address.rsplit(":",1)
    host=host.strip("[]")
    try:
        port=int(port_text)
    except ValueError as exc:
        raise ValueError("Server port must be an integer") from exc
    if not 1<=port<=65535:
        raise ValueError("Server port must be between 1 and 65535")
    signing_key=load_release_private_key(signing_key_path)
    backend_process=None
    if backend_module_path:
        import importlib.util
        backend_path=os.path.abspath(backend_module_path)
        if not os.path.isfile(backend_path):
            raise FileNotFoundError(backend_path)
        spec=importlib.util.spec_from_file_location("ripdir_server_backend",backend_path)
        if spec is None or spec.loader is None:
            raise RuntimeError("Unable to load backend module")
        module=importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        backend_process=getattr(module,"process",None)
        if not callable(backend_process):
            raise ValueError("Backend module must define process(operation, payload, context)")
    def read_policy()->Dict[str,object]:
        with open(policy_path,"rb") as source:
            raw=source.read(1024*1024+1)
        if len(raw)>1024*1024:
            raise ValueError("License policy file exceeds 1 MiB")
        policy=json.loads(raw.decode("utf-8"))
        if not isinstance(policy,dict) or policy.get("enabled") is not True:
            raise PermissionError("Licensing is disabled")
        return policy
    def authorized_device(policy:Dict[str,object],device_id:str,binary_digest:str)->Dict[str,object]:
        devices=policy.get("devices",{})
        device=devices.get(device_id) if isinstance(devices,dict) else None
        if not isinstance(device,dict) or device.get("enabled") is not True:
            raise PermissionError("Device is not licensed")
        allowed_hashes=device.get("binary_sha256",[])
        if not isinstance(allowed_hashes,list) or binary_digest not in allowed_hashes:
            raise PermissionError("Executable is not licensed for this device")
        return device
    class Handler(http.server.BaseHTTPRequestHandler):
        server_version="ripdir-service"
        sys_version=""
        def log_message(self,format_string:str,*args)->None:
            sys.stderr.write("ripdir-service: "+(format_string%args)+"\n")
        def _respond(self,status:int,value:Dict[str,object])->None:
            encoded=canonical_json(value)
            self.send_response(status)
            self.send_header("Content-Type","application/json")
            self.send_header("Cache-Control","no-store")
            self.send_header("X-Content-Type-Options","nosniff")
            self.send_header("Content-Length",str(len(encoded)))
            self.end_headers()
            try:
                self.wfile.write(encoded)
            except (BrokenPipeError,ConnectionResetError):
                pass
        def _read_json(self,limit:int)->Dict[str,object]:
            try:
                length=int(self.headers.get("Content-Length","0"))
            except ValueError as exc:
                raise ValueError("Invalid request Content-Length") from exc
            if not 1<=length<=limit:
                raise ValueError("Request size is outside the allowed range")
            raw=self.rfile.read(length)
            if len(raw)!=length:
                raise ValueError("Truncated request")
            value=json.loads(raw.decode("utf-8"))
            if not isinstance(value,dict):
                raise ValueError("Request must be a JSON object")
            return value
        def do_GET(self)->None:
            if self.path=="/health":
                self._respond(200,{"service":"ripdir-service","status":"ok","backend_enabled":backend_process is not None})
            else:
                self._respond(404,{"error":"not found"})
        def do_POST(self)->None:
            if self.path=="/v1/lease":
                try:
                    request=self._read_json(8192)
                    now=int(time.time())
                    timestamp=int(request.get("timestamp",0))
                    if abs(now-timestamp)>90:
                        raise ValueError("Request timestamp is outside the allowed window")
                    device_id=str(request.get("device_id",""))
                    binary_digest=str(request.get("binary_sha256",""))
                    challenge=str(request.get("challenge",""))
                    if len(device_id)!=64 or any(char not in "0123456789abcdef" for char in device_id.lower()):
                        raise ValueError("Invalid device identifier")
                    if len(binary_digest)!=64 or any(char not in "0123456789abcdef" for char in binary_digest.lower()):
                        raise ValueError("Invalid executable digest")
                    if len(challenge)!=48 or any(char not in "0123456789abcdef" for char in challenge.lower()):
                        raise ValueError("Invalid challenge")
                    if request.get("product")!=APP_NAME:
                        raise ValueError("Unknown product")
                    policy=read_policy()
                    authorized_device(policy,device_id,binary_digest)
                    lease_seconds=int(policy.get("lease_seconds",900))
                    if not 60<=lease_seconds<=30*24*60*60:
                        raise ValueError("Policy lease_seconds must be between 60 seconds and 30 days")
                    payload={"product":APP_NAME,"allowed":True,"binary_sha256":binary_digest,"device_id":device_id,"challenge":challenge,"issued_at":now,"expires_at":now+lease_seconds}
                    signature=signing_key.sign(LICENSE_SIGNATURE_CONTEXT+canonical_json(payload))
                    self._respond(200,{"payload":payload,"signature":base64.b64encode(signature).decode("ascii")})
                except PermissionError as exc:
                    self._respond(403,{"error":str(exc)})
                except Exception as exc:
                    self._respond(400,{"error":str(exc)})
                return
            if self.path=="/v1/execute":
                if backend_process is None:
                    self._respond(404,{"error":"server-side backend is not configured"})
                    return
                try:
                    request=self._read_json(65536)
                    lease=request.get("lease")
                    if not isinstance(lease,dict) or not isinstance(lease.get("payload"),dict):
                        raise PermissionError("A signed authorization lease is required")
                    lease_payload=lease["payload"]
                    lease_signature=base64.b64decode(lease.get("signature",""),validate=True)
                    signing_key.public_key().verify(lease_signature,LICENSE_SIGNATURE_CONTEXT+canonical_json(lease_payload))
                    now=int(time.time())
                    device_id=str(lease_payload.get("device_id",""))
                    binary_digest=str(lease_payload.get("binary_sha256",""))
                    if lease_payload.get("product")!=APP_NAME or lease_payload.get("allowed") is not True:
                        raise PermissionError("Lease does not authorize execution")
                    if int(lease_payload.get("expires_at",0))<now or int(lease_payload.get("issued_at",0))>now+90:
                        raise PermissionError("Lease is expired or not yet valid")
                    policy=read_policy()
                    device=authorized_device(policy,device_id,binary_digest)
                    operation=request.get("operation")
                    if not isinstance(operation,str) or not operation or len(operation)>128 or any(char not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._-" for char in operation):
                        raise ValueError("Invalid backend operation name")
                    allowed_operations=device.get("operations",policy.get("operations",[]))
                    if not isinstance(allowed_operations,list) or operation not in allowed_operations:
                        raise PermissionError("Backend operation is not allowed for this device")
                    request_id=str(request.get("request_id",""))
                    if len(request_id)!=32 or any(char not in "0123456789abcdef" for char in request_id.lower()):
                        raise ValueError("Invalid backend request identifier")
                    result=backend_process(operation,request.get("payload"),{"device_id":device_id,"binary_sha256":binary_digest,"lease_expires_at":int(lease_payload["expires_at"])})
                    result_bytes=canonical_json(result)
                    if len(result_bytes)>1024*1024:
                        raise ValueError("Backend result exceeds 1 MiB")
                    response_payload={"product":APP_NAME,"allowed":True,"operation":operation,"request_id":request_id,"device_id":device_id,"binary_sha256":binary_digest,"issued_at":now,"expires_at":min(int(lease_payload["expires_at"]),now+60),"result":result}
                    signature=signing_key.sign(LICENSE_SIGNATURE_CONTEXT+canonical_json(response_payload))
                    self._respond(200,{"payload":response_payload,"signature":base64.b64encode(signature).decode("ascii")})
                except PermissionError as exc:
                    self._respond(403,{"error":str(exc)})
                except Exception as exc:
                    self._respond(400,{"error":str(exc)})
                return
            self._respond(404,{"error":"not found"})
    class Server(http.server.ThreadingHTTPServer):
        daemon_threads=True
        allow_reuse_address=True
    server=Server((host,port),Handler)
    print(f"ripdir service listening on {host}:{port}")
    print("Run behind a trusted TLS reverse proxy and firewall; the built-in service speaks HTTP.")
    if backend_process is not None:
        print("Server-side backend enabled; policy entries must explicitly allow each operation.")
    try:
        server.serve_forever(poll_interval=0.5)
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
def main(argv:Optional[Sequence[str]]=None)->int:
    try:
        enforce_runtime_protection()
    except Exception as exc:
        print(f"{APP_NAME}: runtime protection failed: {exc}",file=sys.stderr)
        return 126
    parser=argparse.ArgumentParser(prog=APP_NAME,description="ripdir encrypted archive with content-defined chunking, archive-local deduplication, recipient envelopes, and signed runtime protection")
    parser.add_argument("--version",action="version",version=f"{APP_NAME} {FORMAT}")
    actions=parser.add_mutually_exclusive_group()
    actions.add_argument("--pack",metavar="DIRECTORY",help="Build a self-extracting archive")
    actions.add_argument("--pack-raw",metavar="DIRECTORY",help="Build a raw binary .ripdir archive")
    actions.add_argument("--list",action="store_true",help="List authenticated archive contents")
    actions.add_argument("--verify",action="store_true",help="Authenticate and verify all canonical file contents")
    actions.add_argument("--extract",metavar="DIRECTORY",help="Restore the archive under DIRECTORY/root-name")
    actions.add_argument("--cat",metavar="PATH",help="Decrypt a stored file to stdout")
    actions.add_argument("--mount",metavar="DIRECTORY",help="Mount the archive read-only using FUSE")
    actions.add_argument("--repair",metavar="OUTPUT",help="Verify and rebuild a Reed-Solomon-protected archive at OUTPUT")
    actions.add_argument("--device-id",action="store_true",help="Print this installation's hashed device identifier for license policy setup")
    parser.add_argument("--archive",metavar="FILE",help="Archive to operate on")
    parser.add_argument("--output",metavar="FILE",help="Output path for --pack or --pack-raw")
    parser.add_argument("--force",action="store_true",help="Replace an existing output")
    parser.add_argument("--overwrite",action="store_true",help="Replace an existing extraction destination")
    parser.add_argument("--strict-consistency",action="store_true",help="Abort if included source files or the source tree changes during packing")
    parser.add_argument("--console-password",action="store_true",help="Use a terminal password prompt while packing")
    parser.add_argument("--password-stdin",action="store_true",help="Read the password from standard input instead of prompting")
    parser.add_argument("--console-mode",action="store_true",help="Force a Windows console in the generated executable")
    parser.add_argument("--allow-unsafe-symlinks",action="store_true",help="Permit absolute or escaping symlink targets during extraction")
    parser.add_argument("--generate-release-key",metavar="FILE",help="Generate an encrypted Ed25519 signing key for protected executables")
    parser.add_argument("--generate-recipient-key",metavar="PREFIX",help="Generate an encrypted recipient key pair")
    parser.add_argument("--recipient-key-type",choices=("x25519","rsa"),default="x25519",help="Key type for --generate-recipient-key")
    parser.add_argument("--recipient-pubkey",action="append",default=[],metavar="PEM",help="Add a recipient public key to an archive; can be repeated")
    parser.add_argument("--recipient-key",action="append",default=[],metavar="PEM",help="Unlock an archive with a recipient private key; can be repeated")
    parser.add_argument("--recipient-only",action="store_true",help="Create an archive without a passphrase envelope; requires a recipient public key or --fido2-recipient")
    parser.add_argument("--fido2-recipient",action="store_true",help="Enroll a FIDO2 authenticator PRF recipient; requires python-fido2 2.x and compatible hardware")
    parser.add_argument("--redundancy",action="store_true",help="Add Reed-Solomon 8+2 shard protection; requires numpy and increases archive size")
    parser.add_argument("--release-signing-key",metavar="FILE",help="Private Ed25519 key used to sign a self-extracting executable")
    parser.add_argument("--bind-host",action="store_true",help="Bind the generated executable to this OS installation")
    parser.add_argument("--anti-debug",action=argparse.BooleanOptionalAction,default=None,help="Enable best-effort runtime debugger/tracer detection in protected builds (enabled by default; use --no-anti-debug to opt out)")
    parser.add_argument("--license-endpoint",metavar="HTTPS_URL",help="Require a signed short-lived lease from this HTTPS endpoint")
    parser.add_argument("--license-public-key",metavar="HEX",help="Pinned 32-byte Ed25519 license-server public key as 64 hex characters")
    parser.add_argument("--serve-license",metavar="HOST:PORT",help="Run the signed lease service; use behind a TLS reverse proxy")
    parser.add_argument("--backend-module",metavar="PY",help="Server-only Python module exporting process(operation, payload, context)")
    parser.add_argument("--backend-endpoint",metavar="HTTPS_URL",help="Embed the HTTPS endpoint for server-side operations in a protected build")
    parser.add_argument("--backend-call",metavar="OPERATION",help="Call an operation on the configured server-side backend")
    parser.add_argument("--payload-json",default="{}",metavar="JSON",help="JSON object/string/array payload for --backend-call")
    parser.add_argument("--server-signing-key",metavar="FILE",help="Private Ed25519 key used by --serve-license")
    parser.add_argument("--license-policy",metavar="JSON",help="Policy JSON for --serve-license")
    args=parser.parse_args(argv)
    try:
        if args.generate_recipient_key is not None:
            conflicting=any((args.pack,args.pack_raw,args.list,args.verify,args.extract,args.cat,args.mount,args.repair,args.archive,args.output,args.device_id,args.serve_license,args.license_endpoint,args.license_public_key,args.generate_release_key,args.recipient_pubkey,args.recipient_key,args.fido2_recipient,args.backend_call,args.backend_endpoint))
            if conflicting:
                parser.error("--generate-recipient-key cannot be combined with archive operations")
            generate_recipient_key(args.generate_recipient_key,args.recipient_key_type)
            return 0
        if args.generate_release_key is not None:
            conflicting=any((args.pack,args.pack_raw,args.list,args.verify,args.extract,args.cat,args.mount,args.repair,args.archive,args.output,args.device_id,args.serve_license,args.license_endpoint,args.license_public_key,args.recipient_pubkey,args.recipient_key,args.fido2_recipient,args.backend_call,args.backend_endpoint))
            if conflicting:
                parser.error("--generate-release-key cannot be combined with archive operations")
            generate_release_key(args.generate_release_key)
            return 0
        if args.device_id:
            print(machine_binding_id())
            return 0
        if args.serve_license is not None:
            if not args.server_signing_key or not args.license_policy:
                parser.error("--serve-license requires --server-signing-key and --license-policy")
            if any((args.pack,args.pack_raw,args.list,args.verify,args.extract,args.cat,args.mount,args.repair,args.device_id,args.archive,args.output,args.release_signing_key,args.license_endpoint,args.license_public_key,args.bind_host,args.anti_debug,args.backend_endpoint,args.backend_call,args.recipient_pubkey,args.recipient_key,args.fido2_recipient)):
                parser.error("--serve-license cannot be combined with archive or client-build operations")
            run_license_server(args.serve_license,args.server_signing_key,args.license_policy,args.backend_module)
            return 0
        if args.pack is not None or args.pack_raw is not None:
            if has_embedded_payload():
                raise RuntimeError("A distributed ripdir extractor cannot create another archive")
            if args.archive is not None:
                parser.error("--archive cannot be combined with --pack or --pack-raw")
            root=os.path.abspath(args.pack or args.pack_raw)
            if args.output is None:
                name=os.path.basename(root.rstrip(os.sep)) or "archive"
                args.output=name+(".ripdir.exe" if args.pack and os.name=="nt" else ".ripdir" if args.pack else ".ripdir.bin")
            if args.console_password and args.password_stdin:
                parser.error("--console-password and --password-stdin cannot be combined")
            if args.recipient_only and not args.recipient_pubkey and not args.fido2_recipient:
                parser.error("--recipient-only requires --recipient-pubkey or --fido2-recipient")
            if args.recipient_only:
                password=None
            else:
                password=get_password(confirm=True,prefer_gui=not args.console_password and not args.password_stdin,stdin=args.password_stdin)
                if password is None:
                    return 0
            if args.pack is not None:
                if not args.release_signing_key:
                    raise ValueError("Protected self-extracting executables require --release-signing-key. Generate one with --generate-release-key KEY.pem")
                build_self_extracting(root,args.output,password,args.force,args.strict_consistency,args.console_mode,args.release_signing_key,args.bind_host,(True if args.anti_debug is None else args.anti_debug),args.license_endpoint or "",args.license_public_key or "",args.recipient_pubkey,args.backend_endpoint or "",args.fido2_recipient,args.redundancy)
            else:
                if args.release_signing_key or args.bind_host or args.anti_debug or args.license_endpoint or args.license_public_key or args.backend_endpoint:
                    raise ValueError("Release-signing, host-binding, anti-debug, and backend options apply only to --pack")
                build_raw(root,args.output,password,args.force,args.strict_consistency,args.recipient_pubkey,args.fido2_recipient,args.redundancy)
            return 0
        if args.backend_call is not None:
            endpoint=args.backend_endpoint or BACKEND_ENDPOINT
            if not endpoint:
                raise ValueError("No backend endpoint is configured in this build")
            if not _ACTIVE_LEASE:
                if not LICENSE_ENDPOINT:
                    raise ValueError("Remote backend calls require a configured signed lease endpoint")
                digest=verify_release_integrity()
                check_remote_lease(digest)
            try:
                payload=json.loads(args.payload_json)
            except json.JSONDecodeError as exc:
                raise ValueError(f"--payload-json is invalid JSON: {exc}") from exc
            print(json.dumps(remote_backend_call(endpoint,args.backend_call,payload),ensure_ascii=False,indent=2))
            return 0
        archive=archive_path_from_args(args)
        if archive is None:
            parser.print_help()
            return 0
        requested=args.list or args.verify or args.extract is not None or args.cat is not None or args.mount is not None or args.repair is not None
        if not requested and has_embedded_payload() and not args.archive:
            return gui_extract(archive,args.password_stdin,args.recipient_key)
        password=None if args.recipient_key else get_password(stdin=args.password_stdin)
        if password is None and not args.recipient_key:
            return 0
        if args.repair is not None:
            if not args.archive:
                raise ValueError("--repair requires --archive to identify the source archive")
            repair_archive(archive,password,args.repair,args.recipient_key)
            return 0
        if args.list:
            list_archive(archive,password,args.recipient_key)
            return 0
        if args.verify:
            count,total=verify_archive(archive,password,lambda i,n,p: print(f"Verified {i}/{n}: {p}",file=sys.stderr),args.recipient_key)
            print(f"Verified {count} canonical files")
            print(f"Verified plaintext: {total:,} bytes")
            return 0
        if args.cat is not None:
            cat_archive(archive,password,args.cat,args.recipient_key)
            return 0
        if args.mount is not None:
            return mount_archive(archive,password,args.mount,args.recipient_key)
        if args.extract is not None:
            container=ArchiveContainer(archive)
            try:
                manifest_reader,header,data_key=load_archive(container,password,args.recipient_key)
                meta=read_manifest_meta(manifest_reader)
                destination=os.path.join(os.path.abspath(args.extract),str(meta["root_name"]))
                restored=transactional_extract(container,manifest_reader,meta,data_key,header,destination,args.overwrite,args.allow_unsafe_symlinks,lambda done,total,name: print(f"Extracted {done:,}/{total:,}: {name}",file=sys.stderr))
                print(f"Extracted to: {restored}")
            finally:
                container.close()
            return 0
        parser.print_help()
        return 0
    except KeyboardInterrupt:
        print("Interrupted",file=sys.stderr)
        return 130
    except Exception as exc:
        print(f"{APP_NAME}: {exc}",file=sys.stderr)
        return 1
if __name__=="__main__":
    raise SystemExit(main())
