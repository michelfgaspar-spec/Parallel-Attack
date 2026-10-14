#!/usr/bin/env python3
"""Validate concrete certificate domains, local rules, child coverage and replay.

Default validation recomputes all profile/allocation/tuple arithmetic and every
matching maximum. --rerun additionally reconstructs ALL rank/label eligibility,
propagation and complete matching graphs from definitions, comparing deterministic
full event streams. This is executable checking, not proof-assistant certification.
"""
import argparse,gzip,hashlib,json,tarfile,tempfile
from contextlib import ExitStack
from pathlib import Path
from collections import Counter,defaultdict
from itertools import product
import cover as C
import arithmetic as A


def require(ok,message):
    if not ok:raise ValueError(message)

class ArchivePath:
    """Read-only file access inside an uncompressed companion tar archive."""
    def __init__(self,archive,name):self.archive,self.name=archive,name
    def __truediv__(self,name):return ArchivePath(self.archive,self.name+'/'+name)
    def __str__(self):return self.name
    def open(self,mode='rb'):
        require(mode=='rb','archive input is read-only')
        member=self.archive.getmember(self.name)
        require(member.isfile(),'archive input is not a regular file: '+self.name)
        return self.archive.extractfile(member)
    def read_text(self):
        with self.open() as stream:return stream.read().decode('utf-8')

def file_sha(path):
    digest=hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''):digest.update(block)
    return digest.hexdigest()

def events(path,manifest):
    require(file_sha(path)==manifest['sha256'],'compressed stream identity '+str(path))
    digest=hashlib.sha256();count=0
    with path.open('rb') as compressed,gzip.GzipFile(fileobj=compressed) as f:
        for raw in f:
            digest.update(raw);e=json.loads(raw)
            require(e['id']==count,'nonsequential event ID '+str(path));count+=1
            yield e
    require(count==manifest['events'] and digest.hexdigest()==manifest['content_sha256'],'content identity '+str(path))

class Capture:
    def __init__(self):self.last=None
    def emit(self,kind,**data):self.last={'kind':kind,**data};return 0

def check_expected(event,capture):
    expected={k:v for k,v in event.items() if k!='id'}
    require(C.canonical(expected)==C.canonical(capture.last),'altered evaluated rule/event '+str(event['id'])+' '+event['kind'])

def restore_row(e):
    return {k:tuple(e[k]) if k in ('alpha','beta','kappa') else e[k] for k in ('n','q','alpha','beta','kappa','M','U','F','N','sigma','Emin','E','C') if k in e}

def validate_n(root,n):
    P=root/('n'+str(n));manifest=json.loads((P/'manifest.json').read_text());rules=json.loads((Path(__file__).parent/'RULES.json').read_text())['rules']
    require(manifest['n']==n and 14<=n<=37,'cardinality scope');require(manifest['status'] in ('closed','unresolved'),'status')
    stages=manifest['stages'];profiles={};depths={};alpha_expected={};alpha_seen=defaultdict(set);kappa_expected={};kappa_seen=defaultdict(set)
    for e in events(P/'profiles.jsonl.gz',stages['profiles']):
        require(e['rule'] in rules,'unregistered profile rule')
        kind=e['kind']
        if kind in ('depth_dispatch','depth_domain'):
            q=e['q'];require(q not in depths,'duplicate q');depths[q]=e
            if kind=='depth_dispatch':
                require((e['rule']=='L2_Q_EQUALS_N' and q==n) or (e['rule']=='I2_Q_LE_3' and 1<=q<=3 and q<n) or (e['rule']=='I1_I5_SMALL_TOTAL_DEPTH' and 4<=q<n and n<=3*q-1 and e['e_min']==4),'invalid depth dispatch')
            else:
                require(4<=q<=n//3 and e['equation']==n-q,'invalid residual depth')
                alpha_expected[e['id']]=set(A.profiles(n,q))
        elif kind in ('alpha_dispatch','alpha_domain'):
            parent=e['parent'];a=tuple(e['alpha']);require(parent in alpha_expected and a in alpha_expected[parent],'invalid alpha')
            require(a not in alpha_seen[parent],'duplicate alpha');alpha_seen[parent].add(a)
            q=next(z['q'] for z in depths.values() if z['id']==parent)
            if e['rule']=='I3_EARLY_EMPTY':require(not any(a[:(q+1)//2-1]),'invalid early-empty')
            elif kind=='alpha_dispatch':
                M,U=A.pair_counts(q,a);s,E,Cmax=C.endpoint(n,q,M,U)
                require((M,U,s,E,Cmax)==(e['M'],e['U'],e['sigma'],e['E'],e['C']) and Cmax<=200,'invalid raw cutoff')
            else:kappa_expected[e['id']]=(q,a)
        elif kind in ('profile_reject','profile_survive'):
            parent=e['parent'];require(parent in kappa_expected,'invalid kappa parent');q,a=kappa_expected[parent];k=tuple(e['kappa'])
            require(len(k)==q-1 and k[0]==0 and all(0<=v<=z for v,z in zip(k,a)),'invalid kappa')
            require(k not in kappa_seen[parent],'duplicate kappa');kappa_seen[parent].add(k)
            sink=Capture();row=C.refine_profile(n,q,a,k,sink,parent);check_expected(e,sink)
            if kind=='profile_survive':row['profile_id']=e['id'];profiles[e['id']]=row
        else:raise ValueError('unknown profile event '+kind)
    require(set(depths)==set(range(1,n+1)),'missing q family')
    require(all(alpha_seen[i]==v for i,v in alpha_expected.items()),'missing alpha family')
    for i,(q,a) in kappa_expected.items():require(kappa_seen[i]=={(0,)+z for z in product(*(range(v+1) for v in a[1:]))},'missing kappa child')
    # Allocation composition families are checked independently of declared counts.
    allocation_levels={};branches={};completes={};allocations={};level_seen=defaultdict(set);profile_roots=Counter();continuations=Counter()
    def previous_h(parent,profile,j):
        if j>=3:
            require(parent in branches,'missing typed allocation branch')
            require(branches[parent]['row']['profile_id']==profile,'wrong typed branch profile')
            return [list(z) for z in branches[parent]['h']]
        require(j==2 and parent==profile,'bad typed allocation root');q=profiles[profile]['q'];return [[0]*(q-1) for _ in range(q+1)]
    for e in events(P/'allocations.jsonl.gz',stages['allocations']):
        require(e['rule'] in rules,'unregistered allocation rule');kind=e['kind']
        if kind=='allocation_level':
            row=profiles[e['profile']];q=row['q'];j=e['j'];h=previous_h(e['parent'],e['profile'],j)
            require((j==2 and e['parent']==e['profile']) or (j>=3 and e['parent'] in branches and j==branches[e['parent']]['j']+1),'allocation level sequence')
            if j==2:profile_roots[e['profile']]+=1
            else:continuations[e['parent']]+=1
            caps=[C.formal(j,t,row['beta'],row['kappa'],q,row['E']+row['F'],exact=True) if t<=j else 0 for t in range(2,q)]
            require(caps==e['coordinate_caps'] and row['kappa'][j-1]==e['required'],'altered coordinate cap')
            allocation_levels[e['id']]={'event':e,'h':h,'row':row}
        elif kind=='allocation_branch':
            level=allocation_levels[e['parent']];base=level['event'];vals=tuple(e['values']);j=base['j'];row=level['row'];q=row['q']
            require(len(vals)==len(base['coordinate_caps']) and sum(vals)==base['required'] and all(0<=v<=z for v,z in zip(vals,base['coordinate_caps'])),'invalid composition')
            require(vals not in level_seen[e['parent']],'duplicate h child');level_seen[e['parent']].add(vals)
            h=[list(z) for z in level['h']]
            for t,v in enumerate(vals,2):h[t][j-1]=v
            bad=next(((t,C.selected_cap(j,t,row['beta'],row['kappa'],h,q,row['E']+row['F'])) for t in range(2,j+1) if sum(h[t][:j])>C.selected_cap(j,t,row['beta'],row['kappa'],h,q,row['E']+row['F'])),None)
            require(bool(bad)==e['reject'] and C.canonical(bad)==C.canonical(e['bad']),'altered h-prefix rule')
            require(e['rule']==('L14_PREFIX' if bad else 'L20_H_COMPOSITION'),'altered allocation rule')
            branches[e['id']]={'h':h,'j':j,'row':row,'reject':bool(bad)}
        elif kind=='allocation_complete':
            branch=branches[e['parent']];row=branch['row'];continuations[e['parent']]+=1
            h=tuple(tuple(z) for z in branch['h']);require(h==tuple(tuple(z) for z in e['h']) and branch['j']==row['q']-1,'altered complete h')
            completes[e['id']]=(row,h)
        elif kind in ('allocation_reject','allocation_survive'):
            row,h=completes[e['parent']];continuations[e['parent']]+=1;sink=Capture();hr=C.refine_allocation(row,h,e['parent'],sink);check_expected(e,sink)
            if hr is not None:hr['allocation_id']=e['id'];allocations[e['id']]=(hr,h)
        else:raise ValueError('unknown allocation event '+kind)
    for i,level in allocation_levels.items():
        cap=level['event']['coordinate_caps'];need=level['event']['required']
        def dist(j,remaining,prefix=()):
            if j==len(cap)-1:
                if 0<=remaining<=cap[j]:yield prefix+(remaining,)
            else:
                for v in range(min(cap[j],remaining)+1):yield from dist(j+1,remaining-v,prefix+(v,))
        require(level_seen[i]==set(dist(0,need)),'missing allocation composition child')
    require(all(profile_roots[i]==1 for i in profiles),'missing profile allocation root')
    require(all(continuations[i]==(0 if b['reject'] else 1) for i,b in branches.items()),'missing allocation continuation')
    require(all(continuations[i]==1 for i in completes),'missing complete-allocation disposition')
    # Every full-e/delta cell and every retained rho is required.
    completes_parent={i:None for i in allocations}
    # Recover the allocation_complete identity explicitly from each disposition.
    for e in events(P/'allocations.jsonl.gz',stages['allocations']):
        if e['kind']=='allocation_survive':completes_parent[e['id']]=e['parent']
    cells=defaultdict(set);rho_cells={};rho_seen=defaultdict(set);surviving_tuples={}
    for e in events(P/'tuples.jsonl.gz',stages['tuples']):
        require(e['rule'] in rules,'unregistered tuple rule');kind=e['kind']
        if kind=='rho_domain':
            row,h=allocations[e['parent']];ee,dd,mm=e['e'],e['delta'],e['m'];require(mm==ee+dd,'bad m=e+delta')
            cell=(ee,dd);require(cell not in cells[e['parent']],'duplicate full-e/delta cell');cells[e['parent']].add(cell)
            lo=max(0,row['q']*dd-row['sigma'],dd-row['N']);hi=min(mm-1,row['q']*mm-row['n']*ee-1,row['q']*mm-201)
            require((lo,hi)==(e['lower'],e['upper']),'altered exact rho intersection')
            rho_cells[e['id']]=(row,h,e)
        elif kind in ('tuple_reject','tuple_survive'):
            row,h,domain=rho_cells[e['parent']];params=tuple(e['params']);ee,dd,mm,rho,c=params
            require((ee,dd,mm)==(domain['e'],domain['delta'],domain['m']) and domain['lower']<=rho<=domain['upper'] and c==row['q']*mm-rho,'invalid tuple')
            require(rho not in rho_seen[e['parent']],'duplicate rho child');rho_seen[e['parent']].add(rho)
            sink=Capture();C.exact_allocation(row,h,params,e['parent'],sink);check_expected(e,sink)
            if kind=='tuple_survive':surviving_tuples[e['id']]=(row,h,params,domain['parent'],row['profile_id'])
        else:raise ValueError('unknown tuple event '+kind)
    for i,(row,h) in allocations.items():require(cells[i]==set(product(range(row['Emin'],row['E']+1),range(sum(row['kappa']),row['F']+1))),'missing full-e/delta cell')
    for i,(row,h,d) in rho_cells.items():require(rho_seen[i]==set(range(d['lower'],d['upper']+1)),'missing retained rho')
    # Stream tree obligations; all admitted children must have a continuation.
    pending={};roots=Counter();current=None;totals=Counter();node_metadata={}
    def expect(i,allowed):pending[i]=Counter(allowed)
    def consume(e):
        parent=e.get('parent')
        if parent is None:return
        kind=e['kind'];pk=node_metadata[parent]['kind']
        allowed_rules={'degree_labels':{'L22_ALL_DEGREES'},'label_node':{'L22_CHILD_DOMAIN'},'label_child':{'L22_ZERO','L22_POSITIVE'},'label_complete':{'L22_EXACT_QUOTAS'},'box':{'L24_L25_JOINT_MAX'},'box_split':{'L26_COVER_SPLIT'},'box_child':{'L26_CHILD'},'unresolved':{'L26_UNRESOLVED'}}
        if kind in allowed_rules:require(e['rule'] in allowed_rules[kind],'altered label/box kind-rule')
        if kind=='box_reject':require((pk=='box' and e['rule']=='L26_MATCHING') or (pk=='box_child' and e['rule']=='L23_EMPTY'),'altered box exclusion rule')
        if kind=='label_reject':require((e['rule']=='L23_EMPTY' and pk=='label_child' and node_metadata[parent]['label']>0) or e['rule']=='L22_QUOTA_LOOKAHEAD','altered label exclusion rule')
        require(parent in pending,'dangling/extra tree event '+str(e['id']))
        key=('label',e['label']) if e['kind']=='label_child' else ('side',e['side']) if e['kind']=='box_child' else 'continuation'
        require(pending[parent][key]>0,'unexpected/duplicate child '+str(e['id']));pending[parent][key]-=1
        if not any(pending[parent].values()):del pending[parent]
    for e in events(P/'labels.jsonl.gz',stages['labels']):
        require(e['rule'] in rules,'unregistered label rule');kind=e['kind']
        if kind=='tuple_complete':
            require(current is not None and e['parent']==current['root'],'invalid tuple completion')
            require(not pending,'missing label/box descendant')
            if e['unresolved']:totals['unresolved']+=len(e['unresolved'])
            current=None;node_metadata.clear();continue
        if kind=='packing_root':
            require(current is None and e['tuple_event'] in surviving_tuples,'invalid packing root');row,h,params,allocation_id,profile_id=surviving_tuples[e['tuple_event']]
            require(e['allocation_event']==completes_parent[allocation_id] and e['profile_event']==profile_id,'incorrect typed packing links')
            require(C.canonical(h)==C.canonical(e['h']) and list(params)==e['params'],'packing h/tuple mismatch');roots[e['tuple_event']]+=1
            current={'root':e['id'],'row':row,'h':h,'params':params};node_metadata[e['id']]=e;expect(e['id'],['continuation']);continue
        consume(e);node_metadata[e['id']]=e
        if kind in ('degree_labels','label_child','box_child','label_complete','box'):expect(e['id'],['continuation'])
        if kind=='label_node':
            choices=[('label',j) for j in e['positive_children']]+([('label',0)] if e['zero_child'] else [])
            require(len(choices)==len(set(choices)) and choices,'empty/duplicate label child domain');expect(e['id'],choices)
        if kind=='box_split':
            parent_box=node_metadata[e['parent']];i=e['coordinate'];lo=parent_box['lower'][i];hi=parent_box['upper'][i]
            require(lo<hi and e['mid']==(lo+hi)//2 and e['children']==[[lo,e['mid']],[e['mid']+1,hi]],'noncovering split');expect(e['id'],[('side',0),('side',1)])
        if kind=='box_child':
            split=node_metadata[e['parent']];original=node_metadata[split['parent']];LL=list(original['lower']);UU=list(original['upper']);i=split['coordinate'];LL[i],UU[i]=split['children'][e['side']]
            require(LL==e['lower'] and UU==e['upper'],'altered box child endpoints')
        if kind=='box':
            row=current['row'];ee,dd,mm,rho,c=current['params']
            T=C.interval_matching([interval for monomial,interval in e['top']]);require(T==e['Tmax'] and e['K']==sum(row['kappa']) and e['s']==sum(row['beta']),'altered joint integer maximum')
            F=e['K']+T
            if e['Rmax'] is not None:
                R=C.residue_matching(e['mandatory']+[interval for monomial,interval in e['top']],mm);require(R==e['Rmax'],'altered joint residue maximum');F=min(F,R-1-e['s'])
            require(F==e['F'] and e['required']==dd,'altered matching cap');current['last_box']=e
        if kind=='box_reject' and e['rule']=='L26_MATCHING':
            parent_box=node_metadata[e['parent']]
            require(e['F']<e['delta'] and e['F']==parent_box['F'] and e['delta']==parent_box['required'],'invalid matching exclusion')
        if kind=='unresolved':totals['unresolved_events']+=1
        # Retain only live ancestor chains, keeping memory bounded by tree depth.
        if len(node_metadata)>512:
            live=set(pending)|{current['root']}
            todo=list(live)
            while todo:
                parent=node_metadata[todo.pop()].get('parent')
                if parent is not None and parent in node_metadata and parent not in live:live.add(parent);todo.append(parent)
            node_metadata={i:z for i,z in node_metadata.items() if i in live}
    require(current is None and not pending,'interrupted final tree')
    require(all(roots[i]==1 for i in surviving_tuples),'missing surviving tuple packing root')
    require((manifest['status']=='closed')==(totals['unresolved_events']==0 and not manifest['unresolved']),'invalid zero-gap closure')
    return {'n':n,'status':manifest['status'],'profile_families':len(profiles),'allocation_families':len(allocations),'packing_roots':sum(roots.values()),'structural_and_local_rules':'checked','label_rank_propagation_graph_correspondence':'requires --rerun full deterministic stream comparison'}


def validate_run(args,root):
    manifest=json.loads((root/'MANIFEST.json').read_text());scope=args.n or manifest['executed_n'];require(all(14<=n<=37 for n in scope),'verifier cardinality outside 14..37')
    for name,digest in manifest['source_hashes'].items():require(C.sha(Path(__file__).parent/name)==digest,'checker source identity '+name)
    result=[]
    for n in scope:
        require(file_sha(root/('n'+str(n))/'manifest.json')==manifest['manifest_hashes']['n'+str(n)],'manifest identity')
        row=validate_n(root,n)
        if args.rerun:
            replay=args.output or Path(tempfile.mkdtemp(prefix='wilf1437-replay-'))
            regenerated=C.run_n(n,replay);original=json.loads((root/('n'+str(n))/'manifest.json').read_text())
            for stage,data in original['stages'].items():require(regenerated['stages'][stage]['content_sha256']==data['content_sha256'],'reexecution mathematical stream mismatch '+stage)
            row['full_reexecution']='identical complete domain/rule/child/graph event streams'
        result.append(row);print(C.canonical(row),flush=True)
    output={'schema_version':1,'checked_n':scope,'results':result,'method':'concrete domain/child/local-rule validation'+(' plus full deterministic definition reexecution' if args.rerun else ''),'limitations':'ordinary-proof-relative Python checking; no independently verified proof assistant or full admitted leaf audit'}
    if args.output:
        args.output.mkdir(parents=True,exist_ok=True);(args.output/'VALIDATION.json').write_text(json.dumps(output,indent=2)+'\n')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('run',type=Path);ap.add_argument('--archive',action='store_true',help='read execution-v1 directly from the tar archive');ap.add_argument('--n',nargs='+',type=int);ap.add_argument('--rerun',action='store_true');ap.add_argument('--output',type=Path);args=ap.parse_args()
    with ExitStack() as stack:
        root=ArchivePath(stack.enter_context(tarfile.open(args.run,'r:')),'execution-v1') if args.archive else args.run
        validate_run(args,root)
if __name__=='__main__':main()
