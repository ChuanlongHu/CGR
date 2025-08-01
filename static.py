# %%
# parse

# decompose

# autred
# output: neqvs,eeqvs,folded pattern

# cardred
# input: folded pattern
# output: transmission plan ( list of vertex pairs)

# query gen
# Qremote template = Qc pattern
# for each pair in transplan
# for each slicing?

# %%


from functools import *
import sys
import itertools
import logging
import sage
import threading
from sage import all
from sage.graphs.graph import Graph as sGraph
from sage.graphs.connectivity import spqr_tree
from sage.graphs.connectivity import TriconnectivitySPQR

logging.basicConfig(format="%(levelname)s|%(asctime)s: %(message)s", level=logging.INFO)
logger = logging.getLogger(__name__)
logger.setLevel(logging.DEBUG)


def log(*args, logtype="debug", sep=" "):
    logger.debug(sep.join(str(a) for a in args))


import queries
import os, sys


def print_current_thread():
    current_thread = threading.current_thread()
    print(f"当前线程: {current_thread.name} (ID: {current_thread.ident})")


def processQuery(qstr, endpoint):
    # qname = os.environ.get('qname') or 'swd-4'
    # qconfig=queries.qs[qname]
    # qstr=qconfig[0]
    # if qname.startswith('swd'):
    #     estExecFile='SWD-static'
    # else:
    #     estExecFile='SG2-static'

    # %%
    print(print_current_thread())

    def powerset(fullset):
        listrep = list(fullset)
        n = len(listrep)
        return [[listrep[k] for k in range(n) if i & 1 << k] for i in range(2**n)]

    # projvars=set(['a','b','d'])
    # nonprojvars=set(['c','e'])
    # for vars in powerset(nonprojvars):
    #     vars=projvars.union(vars)
    #     log(f"vars={vars}")
    #     # gen edges by rules
    #     # some are must, some are suggest

    #     # search nondetermined edges

    import datetime

    _st = datetime.datetime.now()
    import rdflib.plugins.sparql as sparql
    import rdflib
    import server.sparser as frsparser

    def parse(q: str):
        return frsparser.parseQuery(q)

    print(qstr)
    ast = frsparser.parseQuery(qstr)
    ast
    from collections import defaultdict

    tps = defaultdict(lambda: defaultdict(list))

    def win2s(win: frsparser.CompValue):
        range = f"RANGE {win['range']['val']}s"
        slide = f"SLIDE {win['slide']['val']}s" if "slide" in win else ""
        rt = f"[{range} {slide}]"
        # log(win,rt)
        return rt

    def walk(ast: sparql.parser.ParseResults, tag):
        for part in ast["part"]:
            if part.name == "StreamGraphPattern":
                walk(part["graph"], (part["term"], win2s(part["window"])))
            elif part.name == "OptionalGraphPattern":
                walk(part["graph"], tag)
            elif part.name == "TriplesBlock":
                log(f"{part}@{tag[0]} win {tag[1]}")
                tps[tag[0]][tag[1]].extend(part["triples"])
            else:
                # raise "Unsupported"
                continue

    walk(ast[1]["where"], ("default", "none"))
    log("tps=", tps)
    vars = defaultdict(set)
    for ss, subq in tps.items():
        # log(f"ss={ss}, subq={subq}")
        for _, triples in subq.items():
            for triple in triples:
                s, p, o = triple
                vars[ss].add(s)
                vars[ss].add(o)
    varlist = (
        set(map(lambda x: x["var"], ast[1]["projection"]))
        if "projection" in ast[1].keys()
        else set().union(*vars.values())
    )
    log("varlist=", varlist)
    projvars = varlist

    # for ss in tps:
    #     joinvars=set()
    #     # for ssj in tps:
    #     #     if(ss!=ssj):
    #     #         joinvars.update(vars[ss].intersection(vars[ssj]))
    #     projvars=varlist.intersection(vars[ss]).union(joinvars)
    #     log(f"{ss}: vars={vars[ss]}, joinvars={joinvars}, projvars={projvars}")
    class IdGen:
        def __init__(self, initval=0):
            self.idcnt = initval

        def gen(self):
            obj_id = self.idcnt
            self.idcnt += 1
            return obj_id

    # build graph
    from networkx import DiGraph

    for ss, subq in tps.items():
        # tBGP=[(triple,win) for triple in triples for win,triples in subq.items()]
        tBGP = [(triple, win) for win, triples in subq.items() for triple in triples]
        log("tBGP=", tBGP)
        nxg = DiGraph()
        # widgen=IdGen()
        # win2id=defaultdict(widgen.gen)
        for tp, win in tBGP:
            s, p, o = tp
            # if not isinstance(s,rdflib.term.Variable):
            #     s=s['localname']
            # if not isinstance(o,rdflib.term.Variable):
            #     o=o['localname']
            nxg.add_edge(s, o, lbl=str(tp[1]["part"][0]["part"][0]["part"]))
        # res=convertNx2pyn(nxg)
        # log(res2nodeequivs(pyn.autgrp(res)))
        break

    # %%
    import pynauty as pyn

    def res2nodeequivs(res):
        _, _, _, orbits, _ = res
        node_equivs = defaultdict(list)
        node2equiv = dict()
        for node, equiv in enumerate(orbits):
            node_equivs[equiv].append(node)
            node2equiv[node] = equiv
        return node_equivs, node2equiv

    # %%
    from networkx import (
        DiGraph,
        convert_node_labels_to_integers,
        from_dict_of_lists,
        to_dict_of_dicts,
        draw_networkx,
    )

    def convertNx2pyn(nxg: DiGraph):
        nds = nxg.nodes
        id2n = dict([(idx, nd) for idx, nd in enumerate(nds)])
        n2id = dict([(nd, idx) for idx, nd in enumerate(nds)])
        nxg = convert_node_labels_to_integers(nxg)
        log("ori", to_dict_of_dicts(nxg))
        eidgen = IdGen(len(nxg.nodes))
        e2id = defaultdict(eidgen.gen)
        id2e = dict()
        adj = defaultdict(list)
        color = defaultdict(set)
        for u, vs in nxg.adjacency():
            for v, attrs in vs.items():
                lbl = attrs["lbl"]
                enode = e2id[(u, v)]
                id2e[enode] = (u, v)
                adj[u].append(enode)
                adj[enode].append(v)
                color[lbl].add(enode)
        pyng = pyn.Graph(eidgen.idcnt, True, adj, [v for k, v in color.items()])
        log("e2id", e2id, "adj", adj)
        vldg = from_dict_of_lists(adj, DiGraph)
        draw_networkx(vldg)
        for k, v in color.items():
            for n in v:
                vldg[n]
        log("vldg", vldg)
        return pyng, id2n, id2e, n2id

    graph = nxg
    pyng, id2n, id2e, n2id = convertNx2pyn(graph)
    _parse = datetime.datetime.now()
    # graph.edges(),pyng,
    id2n, id2e, n2id

    # %%
    eqv, n2eqv = res2nodeequivs(pyn.autgrp(pyng))
    eqv

    # %%
    eeqvid = IdGen(len(nxg.nodes))
    eeqvid = defaultdict(eeqvid.gen)
    e2eqv = {}
    eeqvs = defaultdict(list)
    for id, e in id2e.items():
        u, v = e
        eeqv = (n2eqv[u], n2eqv[v])
        e2eqv[id] = eeqvid[eeqv]
        eeqvs[eeqvid[eeqv]].append(id)
    e2eqv, eeqvid, eeqvs

    # %%
    from queue import Queue
    import itertools

    revadj = defaultdict(list)
    for u, vs in pyng.adjacency_dict.items():
        for v in vs:
            revadj[v].append(u)
    log("revadj=", revadj)
    slicing = {}
    for vs in eqv.values():
        if vs[0] in slicing:
            continue
        # expand
        # pick an vertex
        if vs[0] in id2n and len(vs) > 1:
            v0 = vs[0]
            nd = id2n[v0]
            log("vs=", vs, "nd=", nd)
            for v in vs:
                slicing[v] = v
            vis = set()
            q = Queue()
            q.put(v0)
            while not q.empty():
                cur = q.get()
                vis.add(cur)
                if cur in slicing and slicing[cur] == -1:
                    continue
                log("cur=", cur)
                # if cur not in pyng.adjacency_dict: #why?
                # continue
                for ev in itertools.chain(
                    pyng.adjacency_dict[cur] if cur in pyng.adjacency_dict else [],
                    revadj[cur],
                ):
                    eqvs = eqv[n2eqv[ev]]
                    e = id2e[ev]
                    d = True if e[0] == cur else False
                    log(ev, eqvs, e, d)
                    if not len(eqvs) > 1:
                        continue
                    nxt = e[1] if d else e[0]
                    log("nxt", nxt)
                    if nxt not in vis:
                        q.put(nxt)
                        for e in eqvs:
                            u, v = id2e[e]
                            if not d:
                                u, v = v, u
                            log(u, v)
                            if v in slicing and slicing[v] != slicing[u]:
                                log("pivot", v)
                                slicing[v] = -1
                            else:
                                slicing[v] = slicing[u]
                    log("slicing", slicing)
        elif vs[0] in id2n:
            slicing[vs[0]] = vs[0]
            None
    slicing

    # %%
    neqvs = defaultdict(dict)  # node eqv set by eqvid,slicing
    for v, slc in slicing.items():
        neqvs[n2eqv[v]][slc] = v
    neqvs

    # %%

    nwedges = dict()
    slc = -1

    def slicingOfEdge(e):
        u, v = id2e[e]
        rt = slicing[u] if slicing[u] != -1 else slicing[v]
        log("slicingof", (u, v), rt)
        return rt

    pred = IdGen()  # new predicates
    nfolded = {}
    # for each edge eqv set, add an edge, merge es in the eeqvset to this kept edge
    for eeqvid, es in eeqvs.items():
        if slc == -1 and len(es) > 1:
            slc = slicingOfEdge(es[0])  # pick a slicing
        if len(es) <= 1:
            u, v = id2e[es[0]]
            eu = n2eqv[u]
            ev = n2eqv[v]
            eeqv = (eu, ev)
            nwedges[eeqv] = (u, v, pred.gen())
            nfolded[eu] = u
            nfolded[ev] = v
            continue
        for e in es:
            if slicingOfEdge(e) == slc:
                u, v = id2e[e]
                log("add", (u, v))
                su = slicing[u]
                sv = slicing[v]
                eu = n2eqv[u]
                ev = n2eqv[v]
                if su != -1:
                    log(u, "->", n2eqv[u])
                    u = eu
                if sv != -1:
                    log(v, "->", n2eqv[v])
                    v = ev
                eeqv = (eu, ev)
                nwedges[eeqv] = (u, v, pred.gen())
                nfolded[eu] = u
                nfolded[ev] = v
    nwedges, nfolded

    # %%
    projvars = set(map(lambda v: nfolded[n2eqv[n2id[v]]], projvars))
    nxg = DiGraph()
    for e in nwedges.values():
        u, v, p = e
        nxg.add_edge(u, v, lbl=p)
    _autgrp = datetime.datetime.now()
    projvars, nxg.edges

    # %%

    sageGraph = sage.graphs.graph.Graph()
    sageGraph.add_edges(nxg.edges())
    bct = sageGraph.blocks_and_cuts_tree()
    sageGraph.edges(), bct.edges(sort=False), bct.vertices(sort=False)

    # %%
    from collections import defaultdict

    import rdflib
    import json
    from io import StringIO
    import re
    from rdflib.plugins.sparql.parser import parseQuery

    import requests

    def request(endpoint, qstr, limit=1000):
        # 设置请求的URL和查询字符串
        url = f"{endpoint}?limit={limit}"

        # 设置请求头
        params = {"query": f"{qstr}", "format": "json"}

        # 发送POST请求
        response = requests.get(url, params=params)

        # 打印响应内容
        if response.status_code == 200:
            output = response.text
            return output
        else:
            print(f"Error: {response.status_code}")
            print(response.text)

    def tp2lst(tp):
        def term2str(term):
            # print('term=',term)
            if "prefix" in term:
                return f"{term['prefix']}:{term['localname']}"
            elif not isinstance(term, tuple):
                return term.toPython()
            else:
                return f"{term[1] if term[1] else ''}:{term[0].toPython()}"

        try:
            p = tp[1]["part"][0]["part"][0]["part"]
            return (f"{term2str(tp[0])}", f"{term2str(p)}", f"{term2str(tp[2])}")
        except Exception as e:
            print("err:", tp)
            global tperror
            tperror = tp
            raise e

    def tp2str(tp):
        def term2str(term):
            # print('term=',term)
            if "prefix" in term:
                return f"{term['prefix']}:{term['localname']}"
            elif not isinstance(term, tuple):
                return term.toPython()
            else:
                return f"{term[1] if term[1] else ''}:{term[0].toPython()}"

        try:
            p = tp[1]["part"][0]["part"][0]["part"]
            return f"{term2str(tp[0])} <{term2str(p)}> {term2str(tp[2])}."
        except Exception as e:
            print("err:", tp)
            global tperror
            tperror = tp
            raise e

    def modify_sparql_query(query_tuple):
        modified_query = query_tuple  # 获取元组中的查询字符串

        # 使用正则表达式查找 SELECT 后的变量部分，并将其替换成 *
        """modified_query = re.sub(
            r"SELECT\s+[^\{]+(?=\s+WHERE)",  # 匹配 SELECT 后到 WHERE 之间的内容
            "SELECT *",  # 直接替换为 SELECT *
            query,
            flags=re.IGNORECASE,
        )"""
        ast_str = parseQuery(modified_query)
        block = ast_str[1]["where"]["part"]
        tps_local = [tp for blk in block if "triples" in blk for tp in blk["triples"]]
        wherepatternlst_loacl = [tp2lst(tp) for tp in tps_local]
        wherepatternlst_loacl = sorted(
            wherepatternlst_loacl, key=lambda pattern: pattern[2][1]
        )
        wherepatternlst_loacl = sorted(
            wherepatternlst_loacl, key=lambda pattern: pattern[0][1]
        )
        wherepatternlst_local_temp = []
        for pattern in wherepatternlst_loacl:
            wherepatternlst_local_temp.append(
                f"{pattern[0]} <{pattern[1]}> {pattern[2]}."
            )
        wherepattern_local = " ".join(wherepatternlst_local_temp)
        modified_query = f"select * where {{ {wherepattern_local} }}"

        return modified_query

    # prefixes = "PREFIX dbo: <http://dbpedia.org/ontology/> PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>"
    # query = "select distinct ?a ?d where {   ?a <http://dbpedia.org/ontology/wikiPageWikiLink> ?b.   ?b <http://dbpedia.org/ontology/relation> ?c.   ?c <http://dbpedia.org/ontology/wikiPageWikiLink> ?d. }"

    query = modify_sparql_query(qstr)
    log(query)
    ast = parseQuery(query)
    blocks = ast[1]["where"]["part"]
    tps = [tp for blk in blocks if "triples" in blk for tp in blk["triples"]]

    wherepattern = "\n".join([tp2str(tp) for tp in tps])

    log(wherepattern)
    prefixes = "\n".join(
        [f"prefix {item['prefix']}: <{item['iri'].toPython()}>" for item in ast[0]]
    )

    wherepatternlst = [tp2lst(tp) for tp in tps]

    output = request(endpoint, prefixes + query, 10000)
    output_json = json.loads(output)

    bindings_1 = output_json["RAWOutput"]["bindings"]
    bindings_1 = json.loads(bindings_1)
    bindings_1 = bindings_1["results"]["bindings"]
    bindings_2 = output_json["results"]["bindings"]

    bindings = bindings_1 + bindings_2

    rdfg_graph = set()

    for item in wherepatternlst:
        for binding in bindings:
            if (item[0][1] in binding) and (item[2][1] in binding):
                subject = binding[item[0][1]]
                if subject["type"] == "uri":
                    subject = rdflib.URIRef(subject["value"])
                else:
                    subject = rdflib.Literal(subject["value"])

                object_ = binding[item[2][1]]
                if object_["type"] == "uri":
                    object_ = rdflib.URIRef(object_["value"])
                else:
                    object_ = rdflib.Literal(object_["value"])

                predicate = rdflib.URIRef(item[1])
                rdfg_graph.add((subject, predicate, object_))

    rdfg = rdflib.Graph()
    for triple in rdfg_graph:
        rdfg.add(triple)

    log(f"sampling on {endpoint}")

    memcache = defaultdict(dict)

    def memfunc(func):
        fmem = memcache[func]

        def wrapper(*args, **kwargs):
            if args not in fmem:
                fmem[args] = func(*args, **kwargs)
            # log(f"{func.__name__}({args}) memerized")
            return fmem[args]

        return wrapper

    def countallres(vars):
        vars = list(vars)
        combs = []
        for ni, i in enumerate(vars):
            for j in vars[ni + 1 :]:
                u = i if i < j else j
                v = j if i < j else i
                combs.append((u, v))
        constemp = "\n".join(
            [
                f"{comb[0].toPython()} est:{comb[0].toPython()[1:]}_{comb[1].toPython()[1:]} {comb[1].toPython()}."
                for comb in combs
            ]
        )
        consq = f"""prefix est: <i://est/> {prefixes} construct {{ {constemp} }} where {{ {wherepattern} }}"""
        log(consq)
        res = rdfg.query(consq)
        return res.graph

    log(print_current_thread())
    cntg = countallres(vars[ss])
    log("query complete")

    @memfunc
    def comb(u, v):
        i = id2n[u]
        j = id2n[v]
        u = i if i < j else j
        v = j if i < j else i
        log("comb", u, v)
        # query
        pred = f"{u.toPython()[1:]}_{v.toPython()[1:]}"
        cntq = f"""prefix est: <i://est/> select (count(*) as ?cnt) where {{?s est:{pred} ?o}}"""
        log(cntq)
        cntres = cntg.query(cntq).bindings[0][rdflib.term.Variable("cnt")].toPython()
        print(u, v, cntres)
        return cntres

    # res=re.match('.+(where|WHERE)(.+)',qstr,re.DOTALL)
    # wherepattern=res.groups()[1]
    blocks = ast[1]["where"]["part"]
    tps = [tp for blk in blocks if "triples" in blk for tp in blk["triples"]]

    def tp2str(tp):
        def term2str(term):
            # print('term=',term)
            if "prefix" in term:
                return f"{term['prefix']}:{term['localname']}"
            elif isinstance(term, tuple):
                return f"{term[1] if term[1] else ''}:{term[0].toPython()}"
            elif isinstance(term, rdflib.term.URIRef):
                return f"<{term.toPython()}>"
            else:
                return term.toPython()

        try:
            p = tp[1]["part"][0]["part"][0]["part"]
            return f"{term2str(tp[0])} {term2str(p)} {term2str(tp[2])}."
        except Exception as e:
            print("err:", tp)
            global tperror
            tperror = tp
            raise e

    # %%
    # import rdflib
    # memcache=defaultdict(dict)
    # def memfunc(func):
    #     fmem=memcache[func]
    #     def wrapper(*args, **kwargs):
    #         if args not in fmem:
    #             fmem[args] = func(*args, **kwargs)
    #         # log(f"{func.__name__}({args}) memerized")
    #         return fmem[args]
    #     return wrapper
    # rdfg=rdflib.Graph()
    # rdfg.parse(data="""
    # @prefix : <http://base/>.

    # :a :to :b, :c, :d, :e, :f, :g.
    # :b :lk :h .
    # :c :lk :h .
    # :d :lk :h .
    # :e :ulk :h .
    # :f :ulk :h .
    # :g :ulk :h .
    # """,format="turtle")
    # rdfg.parse(open('sstream'),format='nt')
    # @memfunc
    # def comb(u,v):
    #     u=id2n[u]
    #     v=id2n[v]
    #     log('comb',u,v)
    #     # build graph
    #     # query
    #     cntq=f"""
    #     prefix : <http://base/>
    #     prefix sib: <http://b/>
    #     prefix sioc: <http://c/>
    #     {prefixes}
    # select distinct {u.toPython()} {v.toPython()}
    # where {{
    # {wherepattern}
    # }}
    # """
    #     log(cntq)
    #     global rdfg
    #     res=rdfg.query(cntq)
    #     return len(res)
    # def s2var(s):
    #     return rdflib.term.Variable(s)
    # # comb(s2var('b'),s2var('c')), comb(s2var('a'),s2var('d'))
    # memcache
    # 采样

    def s2var(s):
        return rdflib.term.Variable(s)

    # comb(s2var('b'),s2var('c')), comb(s2var('a'),s2var('d'))
    def fullcomb(vset: set):
        return len(vset)

        @memfunc
        def _fullcomb(vs):
            qstr = f"""
        {prefixes}
        select distinct {' '.join(map(lambda v: id2n[v].toPython(),vs))}
        {{ {wherepattern} }}
        """
            log(qstr)
            return len(rdfg.query(qstr))

        return _fullcomb(tuple(sorted(list(vset))))

    memcache

    # %%

    def costfunc(func):
        def wrapper(*args, **kwargs):
            result = func(*args, **kwargs)
            log(f"resof {func.__name__}({args})={result}")
            return result

        return wrapper

    def dfsentry(func):
        def wrapper(*args, **kwargs):
            log(f"{func.__name__}({args})")
            return func(*args, **kwargs)

        return wrapper

    def spqrTree(block: sGraph):
        spqr = TriconnectivitySPQR(block)
        spqr.print_triconnected_components()
        return spqr

    @costfunc
    def blockplan(block: sGraph, mrealnodes: set):
        best = sys.maxsize
        # non-decompose

        # decompose
        spqr = spqrTree(block)
        mrealnodes = mrealnodes.intersection(block.vertices())
        log("blockplan of", block.vertices(), "spqr=", spqr, "mreal=", mrealnodes)

        def nodesOfTricomp(tricomp):
            edges = tricomp[1]
            nodes = set()
            for e in edges:
                nodes.add(e[0])
                nodes.add(e[1])
            return nodes

        def isVEdge(e):
            return e[2] and "newVEdge" in e[2]

        def vEdgesOfTricomp(tricomp):
            return filter(isVEdge, list(tricomp[1]))

        def cutsOfTricomp(tricomp):
            cuts = set()
            for e in vEdgesOfTricomp(tricomp):
                cuts.add(e[0])
                cuts.add(e[1])
            return cuts

        # find must-kept tricomps
        tricomps = list(
            map(lambda t: (t[0], tuple(t[1])), spqr.get_triconnected_components())
        )
        # spqrgraph:sGraph=spqr.get_spqr_tree()
        spqredges = defaultdict(list)
        spair2tricomp = defaultdict(list)
        vedges = {}
        spqrgraph = sGraph()
        log("tricomps", tricomps)
        v2tricomp = defaultdict(set)
        for tricomp in tricomps:
            # log('newVEdgesOf',tricomp,'=',list(vEdgesOfTricomp(tricomp)))
            for e in vEdgesOfTricomp(tricomp):
                # log(e)
                spqredges[e[2]].append(tricomp)
                spair = tuple(sorted(e[:-1]))
                vedges[e[2]] = spair
                spair2tricomp[spair].append(tricomp)
            for node in nodesOfTricomp(tricomp):
                v2tricomp[node].add(tricomp)
            # cutnodes=cutsOfTricomp(tricomp)
            # if(tricomp[0]=='Polygon' or tricomp[0]=='Rigid'):
            #     if(len(list(filter(lambda node:node in mrealnodes and node not in cutnodes,nodesOfTricomp(tricomp))))>1):
            #         mnodes.add(tricomp)
            #     elif(len(list( filter(lambda node:node in mrealnodes and node in cutnodes,nodesOfTricomp(tricomp)) ))>2):
            #         mnodes.add(tricomp)
            # else:
            #     log('tricomp',nodesOfTricomp(tricomp))
            #     nonMnodes.add((tricomp[0],tuple(tricomp[1])))
        # log('must-kept tricomps',mnodes,'non-m',nonMnodes)
        spqrgraph.add_vertices(tricomps)
        spqrgraph.add_edges([(uv[0], uv[1], ve) for ve, uv in spqredges.items()])
        log("spqr edges", spqredges, "spqr graph", spqrgraph)
        # select a root
        startnode = list(v2tricomp[list(mrealnodes)[0]])[0]
        subcnt = defaultdict(lambda: 0)

        def dfs(u, prnt=None):
            subcnt[u] = (
                1 if any(map(lambda v: v in mrealnodes, nodesOfTricomp(u))) else 0
            )
            for v in spqrgraph.neighbor_iterator(u):
                if v != prnt:
                    dfs(v, u)
                    subcnt[u] += subcnt[v]

        dfs(startnode)
        mSpair = {}  # whether a separation pair is must-kept
        costOfSpair = defaultdict(lambda: 0)
        planOfSpair = defaultdict(list)
        blockcost = 0

        @costfunc
        def tricompcost(tricomp, entrySpair):
            @costfunc
            def spaircost(spair):
                rt = (
                    (costOfSpair[spair], planOfSpair[spair])
                    if spair != entrySpair
                    else (sys.maxsize, [])
                )
                if not mSpair[spair] and comb(e[0], e[1]) < costOfSpair[spair]:
                    rt = (comb(e[0], e[1]), [(e[0], e[1])])
                return rt

            @costfunc
            def edgecost(e):
                if e[2] in vedges:
                    spair = vedges[e[2]]
                    return spaircost(spair)
                return (comb(e[0], e[1]), [(e[0], e[1])])

            @costfunc
            def edgecost1(e):
                spair = tuple(sorted(e))
                if spair in mSpair:
                    return spaircost(spair)
                return (comb(e[0], e[1]), [(e[0], e[1])])

            @costfunc
            def chaincost(chainnodes):
                dp = {}
                st = chainnodes[0]
                for i in chainnodes[1:]:
                    dp[i] = edgecost1((st, i))
                for i in chainnodes[2:]:
                    for j in chainnodes[1:]:
                        if j == i:
                            break
                        # dp[i]=min(dp[i],dp[j]+edgecost1(j,i))
                        ecost = edgecost1((j, i))
                        nwcost = dp[j][0] + ecost[0]
                        if dp[i][0] > nwcost:
                            nwplan = dp[j][1].copy()
                            nwplan.append(ecost[1])
                            dp[i] = (nwcost, nwplan)
                return dp[chainnodes[-1]]

            # cost of this tricomp
            tricompcost = 0
            tricompplan = []
            # split at mverts (input & m-spair)
            nodes = nodesOfTricomp(tricomp)
            tricompg = sGraph(list(tricomp[1]))
            mInTricomp = (
                nodes.intersection(mrealnodes)
                .union(list(entrySpair))
                .union(
                    [
                        ee
                        for e in filter(
                            lambda e: isVEdge(e) and mSpair[vedges[e[2]]],
                            tricompg.edges(),
                        )
                        for ee in [e[0], e[1]]
                    ]
                )
            )
            log("tricompg", tricompg.edges())
            log(
                "tricomp non-m",
                nodes.difference(mInTricomp),
                "mreal",
                mrealnodes,
                "m-vert in tricomp",
                mInTricomp,
            )

            # compare fallback plan
            fbcost = len(mInTricomp) * fullcomb(mInTricomp)  # TODO not real cost
            fbplan = [("--", mInTricomp)]

            if tricomp[0] == "Polygon":
                startnode = mInTricomp.pop()
                mInTricomp.add(startnode)
                seq = itertools.chain(
                    tricompg.depth_first_search(startnode), [startnode]
                )
                seg = [startnode]
                # log('seq',list(seq))
                for u in itertools.islice(seq, 1, None):
                    seg.append(u)
                    log("seg+=", u, u in mInTricomp)
                    if u in mInTricomp:
                        if tuple(sorted(seg)) != entrySpair:  # 排除entry edge
                            log("seg", seg)
                            delta = (
                                chaincost(seg)
                                if len(seg) > 2
                                else (edgecost1(tuple(sorted(seg))))
                            )
                            log("here", tricompcost, delta)
                            tricompcost += delta[0]
                            tricompplan.extend(delta[1])
                        # reset
                        seg = [u]
                if (
                    len(mInTricomp) == 2 and len(entrySpair) == 0
                ):  # corner case, can be an edge
                    u = mInTricomp.pop()
                    v = mInTricomp.pop()
                    nwcost = comb(u, v)
                    if nwcost < tricompcost:
                        tricompcost = nwcost
                        tricompplan = [(u, v)]
            elif tricomp[0] == "Triconnected":
                for e in tricomp[1]:
                    # not entry edge
                    if sorted([e[0], e[1]]) != entrySpair:
                        # if not mspair, cost=min(comb,spair)
                        delta = edgecost(e)
                        tricompcost += delta[0]
                        tricompplan.append(delta[1])
            else:
                if len(entrySpair) and mSpair[entrySpair]:
                    # if has real edge
                    for e in tricomp[1]:
                        if not isVEdge(e):
                            tricompcost = comb(e[0], e[1])
                            tricompplan.append((e[0], e[1]))
                            break
                None
            if len(entrySpair):
                costOfSpair[entrySpair] += tricompcost
                planOfSpair[entrySpair].append(tricompplan)
            if tricompcost > fbcost:
                return fbcost, fbplan
            return tricompcost, tricompplan

        @dfsentry
        def dfs1(u, prnt=None, entrySpair=[]):
            ori = subcnt[u] + subcnt[prnt]
            # cost & m-vert of vedges
            for e in spqrgraph.edges_incident(u):
                v = e[1] if e[0] == u else e[0]
                lbl = e[2]
                # log(f"v={v},lbl={lbl}")
                if v != prnt:
                    # vedge to seperation pair
                    subcnt[u] = ori - subcnt[v]
                    spair = vedges[lbl]
                    log(f"separation pair={spair}")
                    # check seperation pair
                    if spair not in mSpair:

                        def checkSpair(spair):
                            # if R and another branch, or S>=2
                            # if S>=2 or S+R+... or R+R+...
                            return (
                                sum(
                                    map(
                                        lambda comp: (
                                            1
                                            if comp[0] != "Bond" and subcnt[comp] > 0
                                            else 0
                                        ),
                                        spair2tricomp[spair],
                                    )
                                )
                                >= 2
                            )

                        mSpair[spair] = checkSpair(spair)
                    dfs1(v, u, spair)
            return tricompcost(u, entrySpair)

        best = dfs1(startnode)
        log(mSpair)
        # def expand(initial):
        #     nodes=set(initial)
        #     color=defaultdict(list)
        #     def dfs(u,c,prnt=None):
        #         color[u].append(c)
        #         for v in spqrgraph.neighbor_iterator(u):
        #             if(v!=prnt and v not in nodes):
        #                 dfs(v,c,u)
        #     for n in initial:
        #         dfs(n,n)
        #     nodes.union([n for n,cs in color.items() if len(cs)>1])
        #     return nodes
        # enumerate valid tree plans
        # nonMnodes=filter(lambda t: t not in mnodes,tricomps)
        # for addon in powerset(nonMnodes):
        #     cost=0
        #     finalMnodes=expand(mnodes.union(addon))
        #     log('addon',addon,'finalMnodes',finalMnodes)
        #     for node in finalMnodes:
        #         cost+=tricost(node)
        #     best=best if best<cost else cost
        return best

    @costfunc
    def treeplan(bct: sGraph, ori: sGraph):
        """
        parameters
        ---
        tree : bc-tree
        """

        def removeBCTLabel(v):
            return v[1]

        def isVnode(v):
            return v[0] == "B" and len(v[1]) > 2

        def nodesOfBlock(v):
            return v[1]

        def blockSubg(blocknodes):
            return ori.subgraph(blocknodes)

        @costfunc
        def nodecost(node, mvertAddon=[]):
            if isVnode(node):
                log(f"+nodecost({node}) mrealnodes:{mrealnodes.union(mvertAddon)}")
                return blockplan(
                    blockSubg(nodesOfBlock(node)), mrealnodes.union(mvertAddon)
                )
            return (0, ())

        def findMustkeptOnTree(tree: sGraph):
            log("tree:", tree.vertices(), tree.edges())
            # must-kept vertices, bct vnode level
            mvertex = set(
                filter(
                    lambda u: (
                        (
                            u[0] == "B"
                            and len(u[1]) > 2
                            and any(map(lambda n: n in projvars, u[1]))
                        )
                        or ((u[0] == "C" or u[0] == "L") and u[1] in projvars)
                    ),
                    tree.vertices(),
                )
            )
            # real vertices
            mrealvertex = projvars.copy()
            # transitive
            msubtreecnt = {}
            startnode = tree.vertices()[0]
            log("projvars:", projvars, "initial mvert:", mvertex, "start:", startnode)

            def dfs1(u):
                # log(u)
                msubtreecnt[u] = 1 if u in mvertex else 0
                for v in tree.neighbor_iterator(u):
                    if not v in msubtreecnt:
                        dfs1(v)
                        msubtreecnt[u] += 1 if msubtreecnt[v] > 0 else 0

            def dfs(u, prnt, prntcnt=0):
                # log(u)
                if msubtreecnt[u] + prntcnt > 2:
                    mvertex.add(u)
                for v in tree.neighbor_iterator(u):
                    if v == prnt:
                        continue
                    b = prntcnt or (
                        msubtreecnt[u] - (1 if msubtreecnt[v] > 0 else 0) > 0
                    )
                    dfs(v, u, 1 if b else 0)
                # 补丁：block的某个cut vert可能有标
                ntype, nodes = u
                if ntype == "B" and len(nodes) > 2:
                    if any(
                        map(lambda v: v[0] == "C" and v in mvertex, tree.neighbors(u))
                    ):
                        mvertex.add(u)
                    if u in mvertex:
                        # real 'block' not bridge
                        for v in tree.neighbor_iterator(u):
                            if (
                                v == prnt
                                and msubtreecnt[prnt] - (1 if msubtreecnt[u] > 0 else 0)
                                > 0
                            ) or (v != prnt and msubtreecnt[v] > 0):
                                if not v[0] == "C":
                                    raise "unexpected"
                                mrealvertex.add(v[1])
                                mvertex.add(v)

            dfs1(startnode)
            msubtreecnt[0] = 0
            log("msubtreecnt", msubtreecnt)
            dfs(startnode, 0)
            # mvertex.difference_update(map(lambda n:('C',n),cuts))
            log("m-vertices:", mvertex, mrealvertex)
            return mvertex, mrealvertex

        treecost = 0
        treeplan = []

        def isedgeblock(v):
            return v[0] == "B" and len(v[1]) == 2

        # add leaf nodes
        edgeblocks = list(filter(lambda v: isedgeblock(v), bct.vertices()))
        cut2block = defaultdict(set)
        cuts = list(
            map(lambda v: v[1], filter(lambda v: (v[0] == "C"), bct.vertices()))
        )
        for bnode in filter(lambda v: isVnode(v), bct.vertices()):
            for v in nodesOfBlock(bnode):
                cut2block[v].add(bnode)
        log("cut2block", cut2block)
        leafs = []
        for e in edgeblocks:
            if e[1][0] not in cuts:
                lfnd = ("L", e[1][0])
                leafs.append(lfnd)
                bct.add_edge(lfnd, e)
                # log('lfnd',lfnd,'from',e)
            if e[1][1] not in cuts:
                lfnd = ("L", e[1][1])
                leafs.append(lfnd)
                bct.add_edge(lfnd, e)
                # log('lfnd',lfnd,'from',e)
            # bct.delete_edge
        log("edges", edgeblocks, "cuts", cuts, "leafs", leafs)
        log("tree", bct.vertices(False))
        # dfs to find must-kept
        mnodes, mrealnodes = findMustkeptOnTree(bct)

        def findChains(tree: sGraph, mvertex: set):
            chains = []

            def dfs(u, stk: list, prnt=None):
                stk.append(u)
                cur = stk
                if u in mvertex:
                    if len(stk) > 1 and any(
                        map(lambda v: v[0] == "B" and len(v[1]) == 2, stk)
                    ):
                        chains.append(stk.copy())
                    cur = [u]
                # log(u,'stk=',stk)
                for v in tree.neighbor_iterator(u):
                    if v != prnt:
                        dfs(v, cur, u)
                stk.pop()

            dfs(list(mvertex)[0], [])
            return chains

        chains = findChains(bct, mnodes)
        log("chains", chains)
        best = {}

        def segcost(u, v):
            if isVnode(u[0]):
                u = u[1][1]
            else:
                u = u[0][1]
            if isVnode(v[0]):
                v = v[1][0]
            else:
                v = v[0][1]
            return comb(u, v), (u, v)

        # chain planning
        for chain in chains:
            bst = sys.maxsize
            # only consider realvertex
            # if two realverts of a block are kept, block can be decomposed
            chainrealnodes = list(
                filter(lambda v: not isedgeblock(v) and not isVnode(v), chain)
            )
            chainnodes = [(chainrealnodes[0], ())]
            # c-B-c: c,c in chain to B
            for prv, cur in zip(chainrealnodes[:-1], chainrealnodes[1:]):
                # prv,cur are realnodes
                # if prv,cur are around a block
                commonblock = cut2block[prv[1]].intersection(cut2block[cur[1]])
                if len(commonblock) > 0:
                    # log(f'prv={prv},cur={cur},common={commonblock}')
                    chainnodes.remove((prv, ()))
                    chainnodes.append(
                        (commonblock.pop(), (removeBCTLabel(prv), removeBCTLabel(cur)))
                    )
                else:
                    chainnodes.append((cur, ()))
            log(
                "chainnodes",
                chainnodes,
                "chain",
                chain,
                "chainrealnodes",
                list(chainrealnodes),
            )
            # chain planning
            """
            dp[i]: cost of st...i, without cost(i)
            st..i=cost(st,i)
            dp[i]=dp[j]+cost(j)+cost(j,i)
            """
            dp = {}
            plan = {}

            def trans(cur, newcost, newplan):
                if newcost < dp[cur]:
                    dp[cur] = newcost
                    plan[cur] = newplan

            st = chainnodes[0]
            for i in chainnodes[1:]:
                sg = segcost(st, i)
                dp[i[0]] = sg[0]
                plan[i[0]] = [sg[1]]
            for i in chainnodes[2:]:
                for j in chainnodes[1:]:
                    if j == i:
                        break
                    log("dpfor2", i, j)
                    # dp[i[0]]=min(dp[i[0]],dp[j[0]]+nodecost(j[0],j[1])+segcost(j,i))
                    nd = nodecost(j[0], j[1])
                    sg = segcost(j, i)
                    nwplan = plan[j[0]].copy()
                    if len(nd[1]):
                        nwplan.append(nd[1])
                    nwplan.append(sg[1])
                    log("nd", nd, "sg", sg, "new plan", nwplan)
                    trans(i[0], dp[j[0]] + nd[0] + sg[0], nwplan)
            log("dp result", dp[chainnodes[-1][0]], plan[chainnodes[-1][0]])
            treecost += dp[chainrealnodes[-1]]
            treeplan.extend(plan[chainrealnodes[-1]])
        # mnodes cost
        for cur in mnodes:
            cost, plan = nodecost(cur)
            treecost += cost
            treeplan.extend(plan)
        return treecost, treeplan

    _cardred_st = datetime.datetime.now()
    plan = treeplan(sageGraph.blocks_and_cuts_tree(), sageGraph)
    log(plan, memcache)

    # %%
    _cardred_end = datetime.datetime.now()
    # plan=(6,[(12, 1), (3, 6), (0, 4), (0, 3), (3, 1), (0, 1)])
    # plan=(1,[(3,7),(0,4),(1,3),(2,3)])
    # plan=(1,[(0,2),(0,3)])

    # %%
    finales = []
    finalpred = IdGen()
    # rclr=defaultdict(set)
    plandup = []
    for finaledge in plan[1]:
        u, v = finaledge
        pred = finalpred.gen()
        if u == "--":
            bn = f"_:{pred}"
            plandup.append((bn, v))
            for m in v:
                # rclr[m].add(bn)
                em = n2eqv[m]
                for slc, mi in neqvs[em].items():
                    finales.append((bn, mi, f"{pred}_{mi}"))
        else:
            plandup.append(finaledge)
            # rclr[u].add((u,v))
            # rclr[v].add((u,v))
            eu = n2eqv[u]
            ev = n2eqv[v]
            if slicing[u] == slicing[v]:
                for slci, ui in neqvs[eu].items():
                    for slcj, vi in neqvs[ev].items():
                        if slci == slcj or slci == -1 or slcj == -1:
                            finales.append((ui, vi, pred))
            else:
                finales.append((u, v, pred))
    # mverts=set(rclr.keys())
    # mverts,rclr,plandup,finales

    # %%
    # for finaledge in plandup:
    #     a,b=finaledge
    #     clr1=defaultdict(set)
    #     color0=a
    #     color1=b
    #     vis=set()
    #     # sg is undirected
    #     # pclosure def: reachable by two verts (undirected), without crossing third mvert
    #     def dfs(u):
    #         vis.add(u)
    #         clr1[u].add(color0)
    #         for v in sageGraph.neighbor_iterator(u):
    #             if v not in vis and v not in mverts:
    #                 dfs(v)
    #     def rdfs(u):
    #         vis.add(u)
    #         clr1[u].add(color1)
    #         for v in sageGraph.neighbor_iterator(u):
    #             if v not in vis and v not in mverts:
    #                 rdfs(v)
    #     if isinstance(a,str):
    #         color=a
    #         for m in list(b):
    #             color0=m
    #             vis=set()
    #             dfs(m)
    #         for m in list(b):
    #             color1=m
    #             vis=set()
    #             rdfs(m)
    #     else:
    #         color=(a,b)
    #         vis=set()
    #         dfs(a)
    #         vis=set()
    #         rdfs(b)
    #     pclosure=[k for k,v in filter(lambda x:len(x[1])>1,clr1.items())]
    #     for u in pclosure:
    #         rclr[u].add(color)
    #     for k,v in filter(lambda x:len(x[1])==1,clr1.items()):
    #         if k not in mverts:
    #             rclr[k].add(v.pop())
    #     log(finaledge,clr1,pclosure,rclr)
    # rclr

    # # %%
    # # ignore single node when has pclosure
    # rclr=dict([(k,set(filter(lambda x: isinstance(x,(tuple,str)),v))
    #         if any(map(lambda x: isinstance(x,(tuple,str)),v)) else v)
    #         for k,v in rclr.items()])
    _validate_end = datetime.datetime.now()
    # rclr

    # %%
    # validate each edge
    def term2str(idOrS):
        if isinstance(idOrS, str):
            return idOrS
        return id2n[idOrS].toPython()

    # srcEdges=defaultdict(list)
    # for u,v,w in sageGraph.edges():
    #     if len(rclr[u].intersection(rclr[v]))>1:
    #         raise Exception(f"edge {u,v} overlapped!")
    #     elif len(
    #         (rclr[u].union([u]))
    #         .intersection(rclr[v].union([v]))
    #         )<1:
    #         raise Exception(f"edge {u,v} empty!")
    #     to=(rclr[u].union([u])).intersection(rclr[v].union([v])).pop()
    #     log(f"edge {(u,v)} -> {to}")
    #     srcEdges[to].append((term2str(u)[1:],term2str(v)[1:]))
    # srcEdges

    # %%

    # constemp=[(term2str(e[0]),f"frsp:rwtt{e[2]}",term2str(e[1]),srcEdges[(e[0],e[1])]) for e in finales]

    constemp = []
    for u, v, p in finales:
        # for ee in [id2e[eid] for eid in eeqvs[eeqvid[(n2eqv[e[0]],n2eqv[e[1]])]]]:
        if isinstance(u, str):
            for slc, vi in neqvs[n2eqv[v]].items():
                constemp.append((term2str(u), f"frsp:rwtt{p}", term2str(vi), None))
        elif len(neqvs[n2eqv[u]]) == 1 and len(neqvs[n2eqv[v]]) == 1:
            constemp.append((term2str(u), f"frsp:rwtt{p}", term2str(v), None))
            continue
        elif slicing[u] == -1 and slicing[v] == -1:
            raise Exception("todo")
        else:
            for slcu, ui in neqvs[n2eqv[u]].items():
                for slcv, vi in neqvs[n2eqv[v]].items():
                    log((ui, vi), (slcu, slcv))
                    if slcu == slcv or slcu == -1 or slcv == -1:
                        constemp.append(
                            (term2str(ui), f"frsp:rwtt{p}", term2str(vi), None)
                        )
    _end = datetime.datetime.now()
    constemp

    # %%
    constempstr = "\n".join([f"{t[0]} {t[1]} {t[2]}." for t in constemp])
    constempstrfixed = "\n".join(
        [
            f"{'?b_'+t[0][2:] if t[0].startswith('_') else t[0]} {t[1]} {t[2]}."
            for t in constemp
        ]
    )
    prefixes += """
    prefix frsp: <http://frsp/>
    """
    # winInMs= os.environ.get('winInMs') or win[0]*win[1]
    qclient = f"""
    {prefixes}
    construct {{ {constempstr} }}
    where {{
        {wherepattern}
    }}
    """
    # qclientext=[[{'n1':srce[0],'n2':srce[1],'w':winInMs} for srce in t[3]] for t in constemp]
    qcentral = f"""
    {prefixes}
    select distinct {' '.join([v.toPython() for v in varlist])}
    where {{
        {constempstrfixed}
    }}
    """
    log(qcentral, qclient)

    # %%
    log(
        f"""
    start at {_st}
    finish using {_end-_st}
    parse using {_parse-_st}
    autgrp using {_autgrp-_parse}
    misc using {_cardred_st-_autgrp}
    cardred using {_cardred_end-_cardred_st}
    validate using {_validate_end-_cardred_end}
    """
    )
    return qcentral, qclient


# %%
from server.utils import *
import json
import os

from flask import Flask, request, jsonify

app = Flask(__name__)


@app.route("/transform", methods=["POST"])
def transform():
    input_string = request.json  # 直接获取请求体中的数据
    log("input:", input_string, request.data)

    if not input_string:
        return "No input provided", 400

    qcentral, qclient = processQuery(input_string["query"], input_string["endpoint"])
    return jsonify({"output1": qcentral, "output2": qclient})


if __name__ == "__main__":
    log(print_current_thread())
    processQuery(
        """
    select ?b ?c where {?a <http://dbpedia.org/ontology/birthPlace> ?b. ?b <http://dbpedia.org/ontology/location> ?d. ?a <http://dbpedia.org/ontology/deathPlace> ?c. ?c <http://dbpedia.org/ontology/location> ?d. }
    """,
        "http://database:3330/DBpedia/query",
    )
    log("======>>>SELFTEST OK!<<<======")
    app.run(host="0.0.0.0", debug=False)
