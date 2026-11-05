#!/usr/bin/env python3
"""Compare prebuilt four-stage HTTP handlers; run from the repository root.

Native programs must be named taro-server, go-server and rust-server in --out.
Use --artifacts with the build.py layout for the seven-language comparison.
Build first; never overlap builds/profiles with this timing campaign. Allocation
counter trials are separate exact-body runs and do not contribute timings.
"""
import argparse, asyncio, hashlib, http.client, json, os, subprocess, sys, time
from pathlib import Path
from types import SimpleNamespace
sys.path.insert(0,'development/benchmarks/json/corpus');import run
sys.path.insert(0,'development/benchmarks/http');import stress
import compare as http_compare
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--out',type=Path,default=Path('target/http-stages'))
parser.add_argument('--connections',type=int,default=64)
parser.add_argument('--rounds',type=int,default=3)
parser.add_argument('--languages',default='taro,go,rust')
parser.add_argument('--artifacts',type=Path,help='build.py artifact layout, including interpreted server sources')
parser.add_argument('--routes',default='/stage/static,/stage/sleep,/stage/encode,/app',help='Comma-separated subset for focused confirmations')
parser.add_argument('--workers',type=int,default=4,help='Runtime workers; Node/Bun remain single-event-loop servers')
args=parser.parse_args()
assert 1 <= args.connections <= 96 and 1 <= args.rounds <= 5
assert 1 <= args.workers <= 8
CONNECTIONS=args.connections
ROUNDS=args.rounds
LANGUAGES=args.languages.split(',')
assert len(set(LANGUAGES))==len(LANGUAGES) and all(x in http_compare.LANGUAGES for x in LANGUAGES)
assert args.artifacts or all(x in ['taro','go','rust'] for x in LANGUAGES)
OUT=args.out.resolve()
subprocess.run(['git','check-ignore','-q',str(OUT/'timing.json')],check=True)
OUT.mkdir(parents=True,exist_ok=True)
run.OUT=OUT;stress.PORT=18183
stress.commands=lambda lang,artifacts,taro:[OUT/(lang+'-server'),str(stress.PORT)]
ARGS=SimpleNamespace(workers=args.workers,bind='127.0.0.1',host='127.0.0.1',max_connections=None,artifacts=Path('target/http-compare/references'),taro=OUT/'taro-server',out=OUT/'timing.json',client_threads=4)
EXPECTED=json.dumps([dict(id=i,message=f'record {i}') for i in range(20)],separators=(',',':')).encode()
ROUTES=args.routes.split(',')
assert len(set(ROUTES))==len(ROUTES) and all(x in ['/stage/static','/stage/sleep','/stage/encode','/app'] for x in ROUTES)
ARTIFACTS=args.artifacts.resolve() if args.artifacts else None
if ARTIFACTS:
 ARGS.artifacts=ARTIFACTS
 files={'taro':[ARTIFACTS.parent/'taro-server'], 'go':[ARTIFACTS/'go-server'],
        'rust':[ARTIFACTS/'rust/target/release/http-comparison'],
        'swift':[ARTIFACTS/'swift/.build/release/Server',ARTIFACTS/'swift/Package.resolved'],
        'node':[ARTIFACTS/'node-runtime',ARTIFACTS/'node/server.mjs'],
        'bun':[ARTIFACTS/'bun-runtime',ARTIFACTS/'bun/server.js'],
        'python':[ARTIFACTS/'venv/bin/python',ARTIFACTS/'python/server.py',ARTIFACTS/'python/requirements.txt']}
 identities={name:{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in files[name]} for name in LANGUAGES}
else:
 identities={name:hashlib.sha256((OUT/(name+'-server')).read_bytes()).hexdigest() for name in LANGUAGES}
identities['configuration']={'connections':CONNECTIONS,'rounds':ROUNDS,'workers':args.workers,'languages':LANGUAGES,'routes':ROUTES,
 'note':'Node/Bun use one event loop; Python uses worker processes; Swift has NIO loops plus its separate global executor'}
identity_path=OUT/'campaign-identities.json'
if identity_path.exists():assert json.loads(identity_path.read_text())==identities,'Binaries changed: choose a new output directory'
else:run.save(identity_path,identities)
rows=json.loads((OUT/'timing.json').read_text()) if (OUT/'timing.json').exists() else []
def save():run.save(OUT/'timing.json',rows)
def quiet():
 deadline=time.monotonic()+180
 while True:
  obs=run.compare.observation();rows.append(dict(kind='load',**obs));save()
  if run.compare.quiet(obs):return
  if time.monotonic()>deadline:raise RuntimeError('Busy: preserving completed samples')
  time.sleep(15)
def request(path):
 c=http.client.HTTPConnection('127.0.0.1',stress.PORT,timeout=15)
 try:
  c.request('GET',path);r=c.getresponse();data=r.read();assert r.status==200
  assert r.getheader('Content-Type','').split(';')[0]=='application/json'
  assert not r.will_close,'all peers must allow keep-alive'
  local=c.sock.getsockname()
  c.request('GET',path);again=c.getresponse();second=again.read();assert again.status==200
  assert c.sock.getsockname()==local,'second exchange must reuse the same connection'
  if path!='/stats':
   # JSON object key order is unspecified (notably Foundation's encoder).
   assert json.loads(data)==json.loads(EXPECTED) and json.loads(second)==json.loads(EXPECTED)
  return data
 finally:c.close()
COUNTER=ARGS.artifacts/'process-usage'
def usage(server):return http_compare.tree_usage(str(COUNTER),server.process.pid)
def start(lang):
 if ARTIFACTS:
  server=http_compare.Server(lang,ARTIFACTS,OUT/f'{lang}-server.log',args.workers)
  stress.PORT=server.port
  return server
 return stress.Server(lang,ARGS)
# Validate every route/body before timings; no profiling/build overlap.
for lang in LANGUAGES:
 server=start(lang)
 try:
  for route in ROUTES:request(route)
 finally:server.close()
for i in range(3):
 quiet()
 if i<2:time.sleep(30)
for round in range(ROUNDS):
 langs=LANGUAGES;offset=round%len(langs);langs=langs[offset:]+langs[:offset]
 offset=round%len(ROUTES);routes=ROUTES[offset:]+ROUTES[:offset]
 for route in routes:
  for lang in langs:
   if any(x.get('kind')=='timing' and x['round']==round and x['language']==lang and x['path']==route for x in rows):continue
   quiet();server=start(lang)
   try:
    warm=stress.wrk(ARGS,route,CONNECTIONS,1,False,2)
    a=usage(server);result=stress.wrk(ARGS,route,CONNECTIONS,1,False,4);b=usage(server)
    errors=sum(result[k] for k in ['connect_errors','read_errors','write_errors','status_errors','timeouts']);assert errors==0,(lang,route,result)
    request(route)
    n=result['requests'];delta={k:b[k]-a[k] for k in ['user_ns','system_ns','instructions','cycles']}
    row=dict(kind='timing',round=round,language=lang,path=route,load_after=run.compare.observation(),**result,**delta)
    row['cpu_ns_per_request']=(delta['user_ns']+delta['system_ns'])/n;row['instructions_per_request']=delta['instructions']/n
    row.update(scenario='stage',connections=CONNECTIONS,depth=1,rss_mib=b['rss']/1024**2,
               cores=(delta['user_ns']+delta['system_ns'])/(result['duration_us']*1000),cpu_us=row['cpu_ns_per_request']/1000)
    rows.append(row);save();print(json.dumps(row),flush=True)
   finally:server.close()
async def fixed_requests(route,count=10000,clients=32):
 async def client(n):
  r,w=await asyncio.open_connection('127.0.0.1',stress.PORT)
  try:
   for _ in range(n):
    w.write(f'GET {route} HTTP/1.1\r\nHost: x\r\n\r\n'.encode());await w.drain()
    h=await asyncio.wait_for(r.readuntil(b'\r\n\r\n'),15);assert h.startswith(b'HTTP/1.1 200')
    size=next(int(x.split(b':',1)[1]) for x in h.split(b'\r\n') if x.lower().startswith(b'content-length:'))
    assert await r.readexactly(size)==EXPECTED
  finally:w.close();await w.wait_closed()
 await asyncio.gather(*(client(count//clients+(i<count%clients)) for i in range(clients)))
for lang in [x for x in LANGUAGES if x in ['taro','go']]:
 for route in ROUTES:
  for round in range(2):
   if any(x.get('kind')=='counter' and x['round']==round and x['language']==lang and x['path']==route for x in rows):continue
   server=start(lang)
   try:
    asyncio.run(fixed_requests(route,1000));a=json.loads(request('/stats'))
    asyncio.run(fixed_requests(route));b=json.loads(request('/stats'))
    delta={k:b[k]-a[k] for k in a}
    row=dict(kind='counter',round=round,language=lang,path=route,requests=10000,**delta);rows.append(row);save();print(json.dumps(row),flush=True)
   finally:server.close()
