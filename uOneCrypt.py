#   uOneCrypt.py: Ubuntu One file ftorage client (Encryption features added) by Carlos del Ojo (deepbit@gmail.com)
#   Copyright (C) 2011 Carlos del Ojo Elias
#   
#   This program is free software; you can redistribute it and/or modify
#   it under the terms of the GNU General Public License as published by
#   the Free Software Foundation; either version 2, or (at your option)
#   any later version.
#   
#   This program is distributed in the hope that it will be useful,
#   but WITHOUT ANY WARRANTY; without even the implied warranty of
#   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#   GNU General Public License for more details.
#   
#   You should have received a copy of the GNU General Public License
#   along with this program; if not, write to the Free Software Foundation,
#   Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. 
#   
#   Written by Carlos del Ojo Elias, deepbit@gmail.com

# This module requires PyCrypto 


from Crypto.Cipher import AES
from StringIO import StringIO
from base64 import b32encode,b64encode,b32decode,b64decode
from urllib import quote,unquote
from urlparse import urlparse
from distutils.version import LooseVersion
import ConfigParser
import hashlib
import hmac
import httplib
import json
import os
import pickle
import random, struct
import re
import sys
import time
import zlib

#python 2.6 at least!

VERSION=LooseVersion("0.1")
CONFIGFILE="uOne.cfg"

class LoginFailed(Exception):
	pass

class FileExists(Exception):
	pass

class FileOrDirNotFound(Exception):
	pass

class NotADirectory(Exception):
	pass

class DirectoryExists(Exception):
	pass

class EOFException(Exception):
	pass

class PathNotCached(Exception):
	pass

class InconsistentCrypt(Exception):
	pass

class BadAuthentication(Exception):
	pass

######################################################################################
########################## Configuration class [ oUbu.cfg ] ##########################
######################################################################################


class Config:
	def __init__(self):
		self.configs=MultiDic()
		self.readFile()

	def readFile(self):
		cfg=ConfigParser.ConfigParser()
		cfg.read(CONFIGFILE)
		self.configs=MultiDic()
		for i in cfg.sections():
			for j in cfg.items(i):
				self.configs[i][j[0]]=j[1]

	def writeFile(self):
		cfg=ConfigParser.ConfigParser()
		data=self.getSource()

		for i,j in data:
			if not cfg.has_section(i.split(":")[0]):
				cfg.add_section(i.split(":")[0])
			cfg.set(i.split(":")[0],":".join(i.split(":")[1:]),j)

		f=open(CONFIGFILE,"w")
		cfg.write(f)
		f.close()


	def readSource(self,source):
		self.configs=MultiDic()
		for i,j in source:
			i=i.split(":")
			item=self.configs
			for k in range(len(i)-1):
				item=item[i[k]]
			item[i[-1]]=j

	def getSource(self):
		data=[]
		for i in self.configs:
			data+=self.getSource2(self.configs,i)
		return data

	def getSource2(self,dic,cur):
		data=[]
		if isinstance(dic[cur.split(":")[-1]],MultiDic):
			for i in dic[cur.split(":")[-1]]:
				data+=self.getSource2(dic[cur.split(":")[-1]],cur+":"+i)
		else:
			return [[cur,dic[cur.split(":")[-1]]]]
		return data

	def __getitem__(self,key):
		return self.configs[key]

	def __setitem__(self,key,value):
		self.configs[key]=value


class MultiDic:
	def __init__(self):
		self.values={}
		pass

	def __getitem__(self,key):
		return self.values.setdefault(key,MultiDic())

	def __setitem__(self,key,value):
		self.values[key]=str(value)

	def __iter__(self):
		return self.values.__iter__()

	def __str__(self):
		return str(self.values)

######################################################################################
########################## Encryption mechanisms [ PyCrypto ] ########################
######################################################################################

class File_Encrypt:
	KEY=None
	NAMEIV=None

	def __init__(self,in_filename=None,data=None,iv=None):
		assert in_filename or data
		if iv:
			self.iv=iv
		else:
			self.iv = ''.join(chr(random.randint(0, 0xFF)) for i in range(16))
		self.encryptor = AES.new(File_Encrypt.KEY, AES.MODE_CBC, self.iv)
		if in_filename:
			self.filesize = os.path.getsize(in_filename)
		elif data:
			self.filesize = len(data)
		self.chunksize=64*1024

		self.out=""
		self.out+=struct.pack('<Q', self.filesize)
		self.out+=self.iv

		self.EOF=False
		if in_filename:
			self.infile=open(in_filename, 'rb')
		elif data:
			self.infile=StringIO(data)
		
		if self.filesize%16:
			self.thelen=len(self.out)+self.filesize+(16-(self.filesize%16))
		else:
			self.thelen=len(self.out)+self.filesize

	def _cread(self):
		chunk = self.infile.read(self.chunksize)
		if len(chunk) == 0:
			raise EOFException()
		elif len(chunk) % 16 != 0:
				chunk += ' ' * (16 - len(chunk) % 16)
		self.out+=self.encryptor.encrypt(chunk)
	
	def __len__(self):
		return self.thelen
		
	def read(self,size=None):
		if size:
			if size>len(self.out) and not self.EOF:
				while len(self.out)<size:
					try:
						self._cread()
					except EOFException as eofe:
						self.EOF=True
						break
			ret,self.out=self.out[:size],self.out[size:]
			return ret
		else:
			if not self.EOF:
				while True:
					try:
						self._cread()
					except EOFException as eofe:
						self.EOF=True
						break
			ret=self.out
			self.out=""
			return ret
			
	@staticmethod
	def decrypt_file(infile, out_filename=None, chunksize=24*1024):
		if not out_filename:
			out_filename = os.path.splitext(in_filename)[0]
	
		origsize = struct.unpack('<Q', infile.read(struct.calcsize('Q')))[0]
		iv = infile.read(16)
		decryptor = AES.new(File_Encrypt.KEY, AES.MODE_CBC, iv)
	
		with open(out_filename, 'wb') as outfile:
			while True:
				chunk = infile.read(chunksize)
				if len(chunk) == 0:
					break
				outfile.write(decryptor.decrypt(chunk))
	
			outfile.truncate(origsize)

	@staticmethod
	def decrypt_str(data, chunksize=24*1024):
		infile=StringIO(data)
		ret=""
	
		origsize = struct.unpack('<Q', infile.read(struct.calcsize('Q')))[0]
		iv = infile.read(16)
		decryptor = AES.new(File_Encrypt.KEY, AES.MODE_CBC, iv)
	
		while True:
			chunk = infile.read(chunksize)
			if len(chunk) == 0:
				break
			ret+=decryptor.decrypt(chunk)

		return ret

######################################################################################
########################## UbuntuOne request Engine [ httplib + Oauth ] ##############
######################################################################################

class UbuRequest:
	AUTH=None
	def __init__(self,method,url,data=None):
		self.url=url.replace(" ","%20")
		self.method=method
		self.data=data
		self.headers={}

	def getVars(self):
		vars=[]
		tmp=urlparse(self.url)[4].split("&")
		if self.method=="POST" and self.data:
			tmp+=self.data.split("&")
		for i in tmp:
			if i:
				if "=" in i:
					vars.append(i.split("=",1))
				else:
					vars.append([i,""])
		return vars

	def perform(self):
		a=httplib.HTTPSConnection(urlparse(self.url)[1])
		if UbuRequest.AUTH:
			self.Oauthenticate()

		a.request(self.method,self.url,self.data,self.headers)

		response=a.getresponse()
		return response



	def Oauthenticate(self):
		timestamp=str(int(time.time()))
		nonce=''.join([str(random.randint(0, 9)) for i in range(8)])
		inivars=[["oauth_consumer_key",UbuRequest.AUTH["consumer_key"].encode()],
				["oauth_token",UbuRequest.AUTH["token"].encode()],
				["oauth_nonce",nonce],
				["oauth_timestamp",timestamp],
				["oauth_signature_method","HMAC-SHA1"],
				["oauth_version","1.0"]]
	
		vs=self.getVars()
		for i,j in vs:
			inivars.append([i,j])
		inivars.sort()
		vars=quote("&".join([i[0]+"="+i[1] for i in inivars]),safe="~")
		up=urlparse(self.url)
		up=quote(up[0]+"://"+up[1].split(":")[0]+up[2],safe="~")
		cad="&".join([self.method,up,vars])
	
		oauth_signature=hmac.new("&".join([quote(UbuRequest.AUTH["consumer_secret"].encode(),safe="~"),quote(UbuRequest.AUTH["token_secret"].encode(),safe="~")]),cad,hashlib.sha1)
		oauth_signature=b64encode(oauth_signature.digest())
	
		inivars=[i for i in inivars if i[0].startswith("oauth_")]
		inivars.insert(0,["OAuth realm",""])#unquote(up)])
		inivars.append(["oauth_signature",quote(oauth_signature,safe="~")])
		Auth=", ".join([i[0]+"="+"\""+i[1]+"\"" for i in inivars])
		self.headers["Authorization"]=Auth

		
		
######################################################################################
########################## FS Cache engine & /CRYPT Path translation #################
######################################################################################

class cacheNode:
	def __init__(self,name,kind,extraInfo=None):
		assert kind in ["f","d"]
		self.name=name
		self.alternativePath=None
		self.kind=kind

		self.cached=False
		self.dirs={}
		self.files={}
		if kind=="d":
			extraInfo={"crypted":False,"keys":[]}
		self.extraInfo=extraInfo

	def __getattr__(self,key):
		if key=="pathname":
			if self.alternativePath!=None:
				return self.alternativePath
			return self.name
		else:
			raise AttributeError

	def addInfo(self,info):
		files,dirs=info
		self.cached=True
		for i in dirs:
			name=i["name"].split("/")[-1]
			self.dirs[name]=cacheNode(name,"d")
			self.dirs[name].extraInfo["crypted"]=self.extraInfo["crypted"]
		for i in files:
			name=i["name"].split("/")[-1]
			self.files[name]=cacheNode(name,"f",{"sha1":i["sha1"],"size":i["size"]})

	def existDir(self,path):
		path=path.strip("/").split("/")

		if len(path)==1:
			if path[0] in self.dirs:
				return True
			elif not path[0] and self.name=="/": # This is root folder
				return True
			return False
		else:
			if path[0] in self.dirs:
				next=path.pop(0)
				path="/".join(path)
				return self.dirs[next].existDir(path)
			return False

	def existFile(self,path):
		path=path.strip("/")

		path=path.split("/")
		if len(path)==1:
			if path[0] in self.files:
				return True
			return False
		else:
			if path[0] in self.dirs:
				next=path.pop(0)
				path="/".join(path)
				return self.dirs[next].existFile(path)
			return False

	def createFile(self,path,extraInfo):
		path=path.strip("/").split("/")

		if len(path)==1:
			if path[0] in self.dirs:
				raise FileExists()
			self.files[path[0]]=cacheNode(path[0],"f",extraInfo)
			if self.extraInfo["crypted"]:
				self.files[path[0]].alternativePath=self.getKey()
		else:
			next=path.pop(0)
			if not next in self.dirs:
				raise NotADirectory()
			path="/".join(path)
			self.dirs[next].createFile(path,extraInfo)

	def createDir(self,path,cached=True):
		path=path.strip("/")

		path=path.split("/")
		if len(path)==1:
			self.dirs[path[0]]=cacheNode(path[0],"d")
			self.dirs[path[0]].extraInfo["crypted"]=self.extraInfo["crypted"]
			self.dirs[path[0]].cached=cached
			if self.extraInfo["crypted"]:
				self.dirs[path[0]].alternativePath=self.getKey()
		else:
			if path[0] not in self.dirs:
				if path[0] in self.files:
					raise FileExists(path[0])
				self.dirs[path[0]]=cacheNode(path[0],"d")
				self.dirs[path[0]].extraInfo["crypted"]=self.extraInfo["crypted"]
				self.dirs[path[0]].cached=cached
				if self.extraInfo["crypted"]:
					self.dirs[path[0]].alternativePath=self.getKey()
			next=path.pop(0)
			path="/".join(path)
			self.dirs[next].createDir(path,cached)

	def deleteDir(self,path):
		path=path.strip("/").split("/")

		if len(path)==1:
			if path[0] in self.dirs:
				if self.dirs[path[0]].alternativePath:
					self.extraInfo["keys"].remove(self.dirs[path[0]].alternativePath)
				del self.dirs[path[0]]
			else:
				raise NotADirectory(path[0])
		else:
			if path[0] in self.dirs:
				next=path.pop(0)
				path="/".join(path)
				self.dirs[next].deleteDir(path)
			else:
				raise NotADirectory(path)

	def deleteFile(self,path):
		path=path.strip("/").split("/")

		if len(path)==1:
			if path[0] in self.files:
				if self.files[path[0]].alternativePath:
					self.extraInfo["keys"].remove(self.files[path[0]].alternativePath)
				del self.files[path[0]]
			else:
				raise FileOrDirNotFound(path[0])
		else:
			if path[0] in self.dirs:
				next=path.pop(0)
				path="/".join(path)
				self.dirs[next].deleteFile(path)
			else:
				raise NotADirectory(path)

	def getKey(self):
		i=0
		while i in (self.extraInfo["keys"]):
			i+=1
		self.extraInfo["keys"].append(i)
		return i

	def getPath(self,path):
		path=path.strip("/").split("/")

		if len(path)==1:
			if path[0] in self.files: return "/"+str(self.files[path[0]].pathname)
			elif path[0] in self.dirs: return "/"+str(self.dirs[path[0]].pathname)
			elif not path[0] and self.name=="/": return "/"
			else: raise FileOrDirNotFound()
		else:
			next=path.pop(0)
			if not next in self.dirs:
				raise NotADirectory()
			return "/"+str(self.dirs[next].pathname)+self.dirs[next].getPath("/".join(path))

	def addExtraInfo(self,path,xtra):
		path=path.strip("/")

		path=path.split("/")
		if len(path)==1:
			if path[0] in self.files: self.files[path[0]].extraInfo=xtra
			elif path[0] in self.dirs: self.dirs[path[0]].extraInfo=xtra
			else: raise FileOrDirNotFound()
		else:
			next=path.pop(0)
			if not next in self.dirs:
				raise NotADirectory()
			self.dirs[next].addExtraInfo("/".join(path),xtra)

	def __getitem__(self,path):
		path=path.strip("/").split("/")

		if len(path)==1:
			if path[0] in self.dirs:
				return self.dirs[path[0]]
			elif not path[0] and self.name=="/":
				return self
			raise NotADirectory(path[0])
		else:
			if path[0] in self.dirs:
				next=path.pop(0)
				path="/".join(path)
				return self.dirs[next][path]
			raise NotADirectory(path[0])

	def prnt(self,indent=0):
		cad=indent*"\t"
		if self.kind=="d" and not self.cached:
			cad+="-"
		elif self.cached:
			cad+="+"
		if self.kind=="d" and self.extraInfo["crypted"]==True:
			cad+="~"+str(self.alternativePath)+"~"
		cad+=self.name+"\n"
		for i in self.files.values():
			cad+=i.prnt(indent+1)
		for i in self.dirs.values():
			cad+=i.prnt(indent+1)
		return cad

	def list(self):
		return self.dirs.keys()+[[i.name,i.extraInfo] for i in self.files.values()]
		

	def listDir(self,path):
		path=path.strip("/").split("/")

		if len(path)==1:
			if path[0] in self.dirs:
				if self.dirs[path[0]].cached==False:
					raise PathNotCached(path)
				return self.dirs[path[0]].list()
			elif not path[0] and self.name=="/":
				return self.list()
			raise FileOrDirNotFound(path)
		else:
			if path[0] in self.dirs:
				next=path.pop(0)
				path="/".join(path)
				return self.dirs[next].listDir(path)
			raise FileOrDirNotFound()


	######## USED ONLY BY /CRYPT

	def dumpInfo(self):
		'''Dumps Info'''
		if self.kind=="f":
			return {"name":self.name,"extrainfo":self.extraInfo,"altPath":self.alternativePath,"kind":"f"}
		else:
			return [{"cached":self.cached,"name":self.name,"extrainfo":self.extraInfo,"altPath":self.alternativePath},[i.dumpInfo() for i in self.files.values()]+[{"kind":"d","cached":False,"name":i.name,"altPath":i.alternativePath} for i in self.dirs.values()]]


	def loadInfo(self,info):
		'''Loads Dumped Info'''
		if self.kind=="f":
			raise Exception("file cacheNode can't use loadInfo Method!")
		self.cached=True
		self.alternativePath=info[0]["altPath"]
		self.name=info[0]["name"]
		self.extraInfo=info[0]["extrainfo"]
		for i in info[1]:
			if i["kind"]=="f":
				self.files[i["name"]]=cacheNode(i["name"],"f",i["extrainfo"])
				self.files[i["name"]].alternativePath=i["altPath"]
			else:
				self.dirs[i["name"]]=cacheNode(i["name"],"d")
				self.dirs[i["name"]].extraInfo["crypted"]=self.extraInfo["crypted"]
				self.dirs[i["name"]].alternativePath=i["altPath"]
				#self.dirs[i[0]["name"]].loadInfo(i)

		
######################################################################################
########################## UbuntuOne rest API wrapper ################################
######################################################################################

class UbuntuOne:

	class Sha1FileWrapper(file):
		def __init__(self,*args,**kwargs):
			file.__init__(self,*args,**kwargs)
			self.sha1=hashlib.sha1()
	
		def read(self,*args,**kwargs):
			x=file.read(self,*args,**kwargs)
			self.sha1.update(x)
			return x
	
		def getSha1(self):
			return self.sha1.hexdigest()

	class Sha1EncFileWrapper(File_Encrypt):
		def __init__(self,*args,**kwargs):
			File_Encrypt.__init__(self,*args,**kwargs)
			self.sha1=hashlib.sha1()
	
		def read(self,*args,**kwargs):
			x=File_Encrypt.read(self,*args,**kwargs)
			self.sha1.update(x)
			return x
	
		def getSha1(self):
			return self.sha1.hexdigest()

	def __init__(self):
		self.consumer_secret=None
		self.consumer_key=None
		self.token=None
		self.token_secret=None

		self.cacheFS=cacheNode("/","d")

		if not CFG["auth"]["key"]:
			print ("YOU MUST FILL AUTH FIELDS IN THE CONFIG FILE uOne.cfg !")
			sys.exit(-1)

		key=hashlib.sha256(CFG["auth"]["key"]).digest()
		tk=[i for i in key.swapcase()]
		tk.reverse()
		tk="".join(tk)
		File_Encrypt.KEY=tk[:32]
		File_Encrypt.NAMEIV=File_Encrypt(data=CFG["auth"]["key"],iv=key[8:24]).read()[8:24]
		File_Encrypt.KEY=key

	def login(self):
		if isinstance(CFG["tokens"]["token"],str):
			UbuRequest.AUTH={"consumer_secret":CFG["tokens"]["consumer_secret"],"consumer_key":CFG["tokens"]["consumer_key"],"token":CFG["tokens"]["token"],"token_secret":CFG["tokens"]["token_secret"]}
		else:
			user=CFG["auth"]["uone_user"]
			passwd=CFG["auth"]["uone_passwd"]
			r=UbuRequest("GET","https://login.ubuntu.com/api/1.0/authentications?ws.op=authenticate&token_name=Ubuntu%20One%20@%20uOneCrypt")
			r.headers["Authorization"]="Basic '%s'" %(b64encode("%s:%s" % (user, passwd)))
			print ("Authenticating...")
			resp=r.perform()
			if resp.status!=200:
				raise BadAuthentication()

			UbuRequest.AUTH=json.loads(resp.read())
			CFG["tokens"]["consumer_secret"]=UbuRequest.AUTH["consumer_secret"]
			CFG["tokens"]["consumer_key"]=UbuRequest.AUTH["consumer_key"]
			CFG["tokens"]["token"]=UbuRequest.AUTH["token"]
			CFG["tokens"]["token_secret"]=UbuRequest.AUTH["token_secret"]
			CFG.writeFile()

			print ("Validating Token... (It may take a few seconds, wait please)")
			a=UbuRequest("GET","https://one.ubuntu.com/oauth/sso-finished-so-get-tokens/"+user)
			resp=a.perform()
	 		if resp.status==200:
				print ("Logged!")
			else:
				print ("Not logged! Wrong credentials or transfer error :S",resp.status,resp.reason)
				raise LoginFailed()

		try:
			self.cachePath("/CRYPT")
		except FileOrDirNotFound as fnf:
			self.createDir("/CRYPT")
			self.cacheFS["/CRYPT"].extraInfo["crypted"]=True



	def _getDirInfo(self,path):
		a=UbuRequest("GET","https://one.ubuntu.com/api/file_storage/v1/~/Ubuntu One"+path+"?include_children=true")
		resp=a.perform()
		if resp.status==404:
			raise FileOrDirNotFound(path)

		info=json.loads(resp.read())
		files=[]
		dirs=[]

		if info["has_children"]==True:
			for i in info["children"]:
				path=i["path"].encode()
				if i["kind"]=="file":
					files.append({"sha1":i["hash"],"path":i["resource_path"].encode(),"size":i["size"],"name":path})
				else:
					dirs.append({"path":i["resource_path"].encode(),"children":i["has_children"],"name":path})

		return files,dirs


	def getNodeInfo(self,path):
		a=UbuRequest("GET","https://one.ubuntu.com/api/file_storage/v1/~/Ubuntu One"+path)
		resp=a.perform()
		if resp.status!=200:
			raise Exception("The information node %s couldn't be retrieved :("%(path))

		node=json.loads(resp.read())
		if node["kind"]=="file":
			return {"sha1":node["hash"],"path":node["resource_path"].encode(),"size":node["size"],"name":node["path"][1:].encode()}
		return {"path":node["resource_path"].encode(),"children":node["has_children"],"name":node["path"][1:].encode()}


	def createFile(self,path,data=None,filename=None,overwrite=False):
		assert path.split("/")>1 and (data or os.path.isfile(filename))

		encrypt=path.strip("/").split("/")[0]=="CRYPT"
		basedir="/".join(path.split("/")[:-1])
		self.cachePath(basedir)
		if not self.cacheFS.existFile(path):
			self.cacheFS.createFile(path,None)
		elif not overwrite:
			raise FileExists(path)

		if data:
			if encrypt:
				info=UbuntuOne.Sha1EncFileWrapper(data=data)
			else:
				info=data   # only case where info is not a file-like object
		else: 
			if encrypt:
				info=UbuntuOne.Sha1EncFileWrapper(in_filename=filename)
			else:
				info=UbuntuOne.Sha1FileWrapper(filename,"rb")

		a=UbuRequest("PUT","https://files.one.ubuntu.com/content/~/Ubuntu One"+self.cacheFS.getPath(path),info)
		resp=a.perform()
		
		if data and not encrypt:	# only case where info is not a file-like object
			sha1=hashlib.sha1()
			sha1.update(info)
			sha1=sha1.hexdigest()
		else:
			sha1=info.getSha1()

		sha1="sha1:"+sha1

		info=self.getNodeInfo(self.cacheFS.getPath(path))
		if info["sha1"]!=sha1:
			raise Exception("The file %s couldn't be created properly!, hashes are different :("%(path))
			### hay que eliminar el fichero tambien!
		else:
			self.cacheFS.addExtraInfo(path,{"sha1":info["sha1"],"size":info["size"]})
			if encrypt:
				self.storeCryptToc(basedir)


	def getContent(self,path,dest,overwrite=False):
		assert path[0]=="/"

		basedir="/".join(path.split("/")[:-1])
		self.cachePath(basedir)
		if not self.cacheFS.existFile(path):
			raise FileNotFound(path)

		if os.path.isdir(dest):
			dest=os.path.join(dest,path.split("/")[-1])

		encrypted=path.strip("/").split("/")[0]=="CRYPT"

		if not overwrite:
			if os.path.isfile(dest):
				raise FileExists(dest)

		a=UbuRequest("GET","https://files.one.ubuntu.com/content/~/Ubuntu One"+self.cacheFS.getPath(path))
		resp=a.perform()

		if resp.status!=200:
			raise FileOrDirNotFould(self.url)

		if encrypted:
			File_Encrypt.decrypt_file(resp,dest)
		else:
			outf=open(dest,"wb")
			data=resp.read(64*1024)
			while data:
				outf.write(data)
				data=resp.read(64*1024)
			outf.close()

	def cachePath(self,path):
		encrypted=path.strip("/").split("/")[0]=="CRYPT"
		if not self.cacheFS.existDir(path) or not self.cacheFS[path].cached:
			if path.strip("/").split("/")[0]:
				basedir="/".join(path.split("/")[:-1])
				self.cachePath(basedir)


			info=self._getDirInfo(self.cacheFS.getPath(path))
			if not encrypted:
				if not self.cacheFS.existDir(path):
					self.cacheFS.createDir(path,False)
				self.cacheFS[path].addInfo(info)
			else:
				self.loadCryptToc(path)
				

	def createDir(self,path):
		assert path[0]=="/"

		encrypted=path.strip("/").split("/")[0]=="CRYPT"
		basedir="/".join(path.split("/")[:-1])
		self.cachePath(basedir)

		if self.cacheFS.existDir(path):
			info=self._getDirInfo(self.cacheFS.getPath(path))
			self.cacheFS[path].addInfo(info)
		else:
			self.cacheFS.createDir(path)
			realPath=self.cacheFS.getPath(path)
			a=UbuRequest("PUT","https://one.ubuntu.com/api/file_storage/v1/~/Ubuntu One"+realPath,'{"kind":"directory"}')
			if encrypted:
				self.storeCryptToc(basedir)
			resp=a.perform()

	def deleteDir(self,path):
		assert path[0]=="/"

		basedir="/".join(path.split("/")[:-1])
		encrypted=basedir.strip("/").split("/")[0]=="CRYPT"
		self.cachePath(basedir)

		if self.cacheFS.existDir(path):
			realPath=self.cacheFS.getPath(path)
			a=UbuRequest("DELETE","https://one.ubuntu.com/api/file_storage/v1/~/Ubuntu One"+realPath,'{"kind":"directory"}')
			resp=a.perform()
			self.cacheFS.deleteDir(path)
			if encrypted:
				self.storeCryptToc(basedir)
		else:
			raise FileOrDirNotFound(path)

	def deleteFile(self,path):
		assert path[0]=="/"

		basedir="/".join(path.split("/")[:-1])
		encrypted=basedir.strip("/").split("/")[0]=="CRYPT"
		self.cachePath(basedir)

		if self.cacheFS.existFile(path):
			realPath=self.cacheFS.getPath(path)
			a=UbuRequest("DELETE","https://one.ubuntu.com/api/file_storage/v1/~/Ubuntu One"+realPath,'{"kind":"directory"}')
			resp=a.perform()
			self.cacheFS.deleteFile(path)
			if encrypted:
				self.storeCryptToc(basedir)
		else:
			raise FileOrDirNotFound(path)

	def listDir(self,path):
		self.cachePath(path)
		return self.cacheFS.listDir(path)

	def storeCryptToc(self,path):
		pickleCrypt=StringIO()
		pickle.dump(self.cacheFS[path].dumpInfo(),pickleCrypt)
		pickleCrypt.seek(0)
		cryptToc=File_Encrypt(data=zlib.compress(pickleCrypt.read()),iv=File_Encrypt.NAMEIV).read()
		qlen=struct.calcsize('Q')
		ln,iv,data=cryptToc[:qlen],cryptToc[qlen:qlen+16],cryptToc[qlen+16:]
		cryptToc=ln+data
		a=UbuRequest("PUT","https://files.one.ubuntu.com/content/~/Ubuntu One%s/.ToC" % (self.cacheFS.getPath(path)),cryptToc)
		resp=a.perform()

	def loadCryptToc(self,path):
		trys=3
		while (trys):
			trys-=1
			a=UbuRequest("GET","https://files.one.ubuntu.com/content/~/Ubuntu One%s/.ToC" % (self.cacheFS.getPath(path)))
			resp=a.perform()
			if resp.status!=200:
				print resp.status,resp.reason,resp.read()
				f,d=self._getDirInfo(self.cacheFS.getPath(path))
				if f or d:
					continue
				if path=="/CRYPT":
					self.cacheFS["/CRYPT"].extraInfo["crypted"]=True
				self.cacheFS[path].cached=True
				break
			else:
				break

		if not trys: raise InconsistentCrypt()

		data=resp.read()
		qlen=struct.calcsize('Q')
		ln,data=data[:qlen],data[qlen:]
		data=ln+File_Encrypt.NAMEIV+data
		data=StringIO(File_Encrypt.decrypt_str(data))
		data.seek(0)
		data=zlib.decompress(data.read())
		a= pickle.load(StringIO(data))
		self.cacheFS[path].loadInfo(a)

	def isDir(self,path):
		return self.cacheFS.existDir(path)

	def isFile(self,path):
		return self.cacheFS.existFile(path)

		


######################################################################################
########################## Console client interface ##################################
######################################################################################

def recur(path,dest,ubuObj):
	all=os.listdir(path)

	files=[i for i in all if os.path.isfile(os.path.join(path,i)) and not os.path.islink(os.path.join(path,i))]
	dirs=[i for i in all if os.path.isdir(os.path.join(path,i)) and not os.path.islink(os.path.join(path,i))]

	for i in dirs:
		ndir=dest+"/"+i
		ndir.replace("//","/")
		ubuObj.createDir(ndir)
		recur(os.path.join(path,i),ndir,ubuObj)

	for i in files:
		npath=dest+"/"+i
		npath.replace("//","/")
		print ("Copying... :",npath)
		try:
			ubuObj.createFile(npath,filename=os.path.join(path,i))
		except FileExists as fe:
			pass

CFG=Config()

if __name__=="__main__":
	import cmd

	try:
		if LooseVersion(UbuRequest("GET","https://raw.github.com/deepbit/uOneCrypt/master/VERSION").perform().read().strip())>VERSION:
			print ("\r\nThis version of is old! Get the new one! (git clone git://github.com/deepbit/uOneCrypt.git)\r\n")
	except:pass



	class uOneCli(cmd.Cmd):
		def __init__(self,prompt):
			cmd.Cmd.__init__(self)
			self.baseprompt=prompt
			self.uone=UbuntuOne()
			self.uone.login()
			self.curPath="/"
			self.updatePrompt()

		def updatePrompt(self):
			self.prompt=self.baseprompt+":"+self.curPath+"> "

		def aproxSize(self,tam):
			if tam<1024: return str(tam)+" Bytes"
			elif tam<1024*1024: return "{0:.1f} Kb".format(tam/1024.0)
			elif tam<1024*1024*1024: return "{0:.1f} Mb".format(tam/1048576.0)
			else: return "{0:.1f} Gb".format(tam/1073741824.0)


		def do_exit(self,pars):
			print ("\r\nExiting... Bye!\r\n")
			sys.exit(0)

		def do_cd(self,pars):
			if pars=="..":
				parts=self.curPath.split("/")[:-1]
				if  len(parts)==1 or pars=="/":
					self.curPath="/"
				else:
					self.curPath="/".join(self.curPath.split("/")[:-1])
			else:
				if pars.startswith("/"):
					fdir=pars
				else:
					if self.curPath=="/":
						fdir="/"+pars.strip("/")
					else:
						fdir=self.curPath+"/"+pars.strip("/")
				if not self.uone.isDir(fdir):
					print ("Directory [%s] doesn't exist." % (fdir))
					return
				self.curPath=fdir
			self.updatePrompt()

		def do_ls(self,pars):
			print ("{0:>12} | {1}".format("Size","Node"))
			print ("-"*80)
			for i in self.uone.listDir(self.curPath):
				if isinstance(i,list):
					print ("{0:>12} | {1}".format(self.aproxSize(i[1]["size"]),i[0]))
				else:
					print ("{0:>12} | {1}/".format("---",i))
			print ("-"*80)

		def do_mkdir(self,pars):
			if pars.startswith("/"):
				fdir=pars
			else:
				fdir=self.curPath+"/"+pars.strip("/")
			self.uone.createDir(fdir)
			print ("Directory %s created\r\n"%(fdir))

		def do_rmdir(self,pars):
			if pars.startswith("/"):
				fdir=pars
			else:
				fdir=self.curPath+"/"+pars.strip("/")
			if not self.uone.isDir(fdir):
				print ("Directory [%s] doesn't exist." % (fdir))
				return
			ans=raw_input("Are you sure you want to remove [%s] and all its children? (y/N) " % (fdir)).strip().lower()
			if ans=="y":
				self.uone.deleteDir(fdir)
				print ("Directory %s deleted\r\n"%(fdir))
			else:
				print ("Cancelled")

		def do_put(self,path):
			if os.path.isfile(path):
				if self.curPath=="/":
					fpath="/"+path.split("/")[-1]
				else:
					fpath=self.curPath+"/"+path.split("/")[-1]

				try:
					self.uone.createFile(fpath,filename=path)
				except FileExists as fe:
					ans=raw_input("File [%s] already exists, do you want to overwrite it? (y/N) " % (fpath)).strip().lower()
					if ans=="y":
						self.uone.createFile(fpath,filename=path,overwrite=True)
					
			elif os.path.isdir(path):
				pass
			else:
				print ("[%s] is neither a file nor a directory." % (path))
				return

		def do_get(self,path):
			if self.curPath=="/":
				fpath="/"+path.split("/")[-1]
			else:
				fpath=self.curPath+"/"+path.split("/")[-1]

			if self.uone.isFile(fpath):
				try:
					self.uone.getContent(fpath,fpath.split("/")[-1])
				except FileExists as fe:
					ans=raw_input("File [%s] already exists in your FS, do you want to overwrite it? (y/N) " % (fpath)).strip().lower()
					if ans=="y":
						self.uone.getContent(fpath,fpath.split("/")[-1],overwrite=True)

			elif self.uone.isDir(fpath):
				pass
			else:
				print ("[%s] is neither a file nor a directory." % (path))
				return

		def do_rm(self,pars):
			if pars.startswith("/"):
				fpath=pars
			else:
				fpath=self.curPath+"/"+pars.strip("/")
			if not self.uone.isFile(fpath):
				print ("File [%s] doesn't exist." % (fpath))
				return
			self.uone.deleteFile(fpath)
			print ("File %s deleted\r\n"%(fpath))
			
			

		########## HELP METHODS ##################
		
		def help_get(self):
			print ("get [path_to_file] - Gets the given file and stores in yout current workin directory")
	
		def help_put(self):
			print ("put [path_to_file] - Copy a local file into the current directory")

		def help_mkdir(self):
			print ("mkdir/md [path] - Creates the given directory (does not create parents if they don't exist!)")

		def help_rmdir(self):
			print ("rmdir/rd [path] - Removes the given directory and its children (USE CAREFULLY)")

		def help_exit(self):
			print ("EOF/exit/quit - Exits uOneCrypt")

		def help_ls(self):
			print ("dir/ls - lists files and directories in the current path")

		def help_cd(self):
			print ("cd [abs./local path] - Change current path")

		def help_rm(self):
			print ("rm/del [path] - Deletes the file specified in the path")

		do_EOF=do_quit=do_exit
		do_dir=do_ls
		do_md=do_mkdir
		do_rd=do_rmdir
		do_del=do_rm
		help_del=help_rm
		help_rd=help_rmdir
		help_md=help_mkdir
		help_dir=help_ls
		help_EOF=help_quit=help_exit


	cli=uOneCli("uOneCrypt")
	cli.cmdloop()
