#!/usr/bin/env python3

import pygraphviz  as pgv
import collections as coll
import os
import uuid

Node                = coll.namedtuple('Node', ['uid','datum'])
Arc                 = coll.namedtuple('Arc', ['fromNode','toNode','datum'])
DiGraph             = coll.namedtuple('DiGraph', ['setOfNodes','setOfArcs'])
FlowArcDatum        = coll.namedtuple('FlowArcDatum', ['capacity','flow'])
FlowArcDatumWithUid = coll.namedtuple('FlowArcDatum', ['capacity','flow','uid'])
FlowNodeDatum       = coll.namedtuple('FlowNodeDatum', ['flowIn','flowOut'])
ResidualDatum       = coll.namedtuple('ResidualDatum', ['residualCapacity','action'])
MaxFlowProblemState = coll.namedtuple('MaxFlowProblemState', ['digraph','sourceNodeUid','terminalNodeUid','maxFlowProblemStateUid'])
Cut                 = coll.namedtuple('Cut', ['setOfCutArcs'])
STCut               = coll.namedtuple('STCut', ['s','t','cut'])

TOL = 10
debug =  False

Bipartition = coll.namedtuple('Bipartition',['firstPart', 'secondPart', 'digraph'])
def bipartition(G):
    nodes = frozenset(G.setOfNodes)
    arcs  = frozenset(G.setOfArcs)
    arcs = arcs.union( frozenset( {Arc(a.toNode,a.fromNode,a.datum) for a in G.setOfArcs} ) )
    H = DiGraph(nodes, arcs)
    H_as_dict = digraph_to_dict(H)
    color = dict([])
    some_node = next(iter(H.setOfNodes))
    deq = coll.deque([some_node])
    color[some_node] = -1
    while len(deq) > 0:
        curr = deq.popleft()
        for a in H_as_dict.get(curr):
            if (a.toNode not in color):
                color[a.toNode] = -1*color[curr]
                deq.extend([a.toNode])
            elif(color[curr] == color[a.toNode]):
                print(curr,a.toNode)
                raise Exception('Not Bipartite.')

    firstPart  = frozenset( {n for n in color if color[n] == -1 } )
    secondPart = frozenset( {n for n in color if color[n] == 1 } )

    if( firstPart.union(secondPart) != G.setOfNodes ):
        raise Exception('Not Bipartite.')

    return Bipartition(firstPart, secondPart, G)

def solve_mbm( bipartition ):
    s = Node(uuid.uuid4(), FlowNodeDatum(0,0))
    t = Node(uuid.uuid4(), FlowNodeDatum(0,0))

    translate = {}
    arcs = frozenset([])
    for a in bipartition.digraph.setOfArcs:
        if ( (a.fromNode in bipartition.firstPart) and (a.toNode in bipartition.secondPart) ):
            fark = Arc(a.fromNode,a.toNode,FlowArcDatum(1,0))
            arcs = arcs.union({fark})
            translate[frozenset({a.fromNode.uid,a.toNode.uid})] = a
        elif ( (a.toNode in bipartition.firstPart) and (a.fromNode in bipartition.secondPart) ):
            bark = Arc(a.toNode,a.fromNode,FlowArcDatum(1,0)) 
            arcs = arcs.union({bark})
            translate[frozenset({a.fromNode.uid,a.toNode.uid})] = a
    arcs1 = frozenset( {Arc(s,n,FlowArcDatum(1,0)) for n in bipartition.firstPart } )
    arcs2 = frozenset( {Arc(n,t,FlowArcDatum(1,0)) for n in bipartition.secondPart } )
    arcs = arcs.union(arcs1.union(arcs2))

    nodes = frozenset( {Node(n.uid,FlowNodeDatum(0,0)) for n in bipartition.digraph.setOfNodes} ).union({s}).union({t})
    G = DiGraph(nodes, arcs)
    mfp = MaxFlowProblemState(G, s.uid, t.uid, 'bipartite') 
    result = edmonds_karp(mfp)

    lookup_set = {a for a in result.digraph.setOfArcs if (a.datum.flow > 0) and (a.fromNode.uid != s.uid) and (a.toNode.uid != t.uid)}
    matching = {translate[frozenset({a.fromNode.uid,a.toNode.uid})] for a in lookup_set}

    return matching

def arc_to_id(arc):
    if(arc.datum):
        label =  '['+str(arc.fromNode.uid)+']'+'['+str(arc.toNode.uid)+']'+'{'+datum_to_str(arc.datum)+'}'
    else:
        label =  '['+str(arc.fromNode.uid)+']'+'['+str(arc.toNode.uid)+']'+'{}'
    #label =  '['+str(arc.fromNode.uid)+']'+'['+str(arc.toNode.uid)+']'
    return label

def datum_to_str(x):
    if (type(x) is FlowNodeDatum):
        #return str(x.flowIn) + '/' + str(x.flowOut)
        return ''
    elif (type(x) is FlowArcDatum):
        return str(x.flow) + '/' + str(x.capacity)
    elif (type(x) is ResidualDatum):
        return str(x.residualCapacity)
    elif (type(x) is WeightArcDatum):
        return str(x.weight)
    elif (type(x) is int or type(x) is str):
        return str(x)
    else:
        return '-'

def node_to_label(node):
    #label = str(node.uid)+'{'+str(node.datum)+'}' if node.datum else str(node.uid)
    label = str(node.uid)+'{'+datum_to_str(node.datum)+'}' if node.datum else str(node.uid)
    return label

def arc_to_label(arc):
    #label = str(arc.datum) if arc.datum else ''
    label = datum_to_str(arc.datum) if arc.datum else ''
    return label

def color_path(apath, G_dot, color='red'):
    dot_G = G_dot.copy()
    arcs  = frozenset(apath)
    nodes = frozenset(path_arcs_to_nodes(apath))
    dot_G = color_nodes(nodes, dot_G, color=color)
    dot_G = color_arcs(arcs, dot_G, color=color)
    return dot_G

def color_arcs_nodes(apath, G_dot, color='red'):
    dot_G = G_dot.copy()
    arcs  = frozenset(apath)
    nodes = frozenset(arcs_to_nodes(apath))
    dot_G = color_nodes(nodes, dot_G, color=color)
    dot_G = color_arcs(arcs, dot_G, color=color)
    return dot_G

def color_nodes(nodes, G_dot, color='red'):
    dot_G = G_dot.copy()
    nodes = frozenset(nodes)
    nids = frozenset({n.uid for n in nodes})
    for n in nids:
        node = dot_G.get_node(n)
        node.attr['color']     = color
        node.attr['fontcolor'] = color
    return dot_G
 
def color_arcs(arcs, G_dot, color='red'):
    dot_G = G_dot.copy()
    arcs  = frozenset(arcs)
    for a in arcs:
        for e in dot_G.edges(nbunch=a.fromNode.uid):
            in_id, out_id = e
            if(a.fromNode.uid == in_id):
                arc_name = arc_to_id(a)
                dot_G.get_edge(in_id,arc_name).attr['color']  = color
                dot_G.get_node(arc_name).attr['fontcolor']    = color
                dot_G.get_edge(arc_name,a.toNode.uid).attr['color'] = color
    return dot_G

def source_nodes(G):
    to_nodes = frozenset([a.toNode for a in G.setOfArcs])
    sources = G.setOfNodes.difference(to_nodes)
    return sources

def terminal_nodes(G):
    from_nodes = frozenset([a.fromNode for a in G.setOfArcs])
    terms      = G.setOfNodes.difference(from_nodes)
    return sources

def example_gdict():
    A = Node('A','')
    B = Node('B','')
    C = Node('C','')
    
    AB = Arc(A,B,'A,B,C, \nit\'s as easy as')
    BC = Arc(B,C,'1,2,3!')
    
    g = {}
    g[A] = frozenset([AB])
    g[B] = frozenset([BC])
    g[C] = frozenset([])

    return g

def example_prop_e():
    s = Node('s',FlowNodeDatum(0.0,1.0))
    A = Node('A',FlowNodeDatum(1.0,1.0))
    B = Node('B',FlowNodeDatum(1.0,1.0))
    t = Node('t',FlowNodeDatum(1.0,0.0))
    
    sA = Arc(s,A,FlowArcDatum(1.0,1.0))
    AB= Arc(A,B,FlowArcDatum(2.0,1.0))
    BA= Arc(B,A,FlowArcDatum(2.0,0.0))
    Bt = Arc(B,t,FlowArcDatum(2.0,1.0))

    nodes = frozenset([s,A,B,t])
    arcs  = frozenset([sA,AB,BA,Bt])
    g = DiGraph(nodes,arcs)
    g_dict = digraph_to_dict(g)
    g_dot = dict_to_dot(g_dict)
    g_dot = color_arcs([sA], g_dot,color='red') 
    g_dot = color_nodes([s,A], g_dot,color='red') 
    g_dot = color_arcs([AB,BA], g_dot,color='green') 
    g_dot = color_arcs([Bt], g_dot,color='blue') 
    g_dot = color_nodes([B,t], g_dot,color='blue') 
    dot_to_file(g_dot,name='prop_e_1')

    ''' ---- '''
    s = Node('s',FlowNodeDatum(0.0,1.0))
    A = Node('A',FlowNodeDatum(2.0,2.0))
    B = Node('B',FlowNodeDatum(2.0,2.0))
    t = Node('t',FlowNodeDatum(1.0,0.0))
 
    sA = Arc(s,A,FlowArcDatum(1.0,1.0))
    AB= Arc(A,B,FlowArcDatum(2.0,2.0))
    BA= Arc(B,A,FlowArcDatum(2.0,1.0))
    Bt = Arc(B,t,FlowArcDatum(2.0,1.0))

    nodes = frozenset([s,A,B,t])
    arcs  = frozenset([sA,AB,BA,Bt])
    g = DiGraph(nodes,arcs)
    g_dict = digraph_to_dict(g)
    g_dot = dict_to_dot(g_dict)
    g_dot = color_arcs([sA], g_dot,color='red') 
    g_dot = color_nodes([s,A], g_dot,color='red') 
    g_dot = color_arcs([AB,BA], g_dot,color='green') 
    g_dot = color_arcs([Bt], g_dot,color='blue') 
    g_dot = color_nodes([B,t], g_dot,color='blue') 

    dot_to_file(g_dot,name='prop_e_2')

    return g

def example_house():
    A = Node('A','Build Foundation.')
    B = Node('B','Affix walls\nto foundation.')
    
    AB = Arc(A,B,'Allows')
    
    G = {}
    G[A] = frozenset([AB])
    G[B] = frozenset([])

    return G

def digraph_to_dict(G):
    G_as_dict = dict([])
    for a in G.setOfArcs:
        if(a.fromNode not in G.setOfNodes):
            err_msg = 'There is no Node {a.fromNode.uid!s} to match the Arc from {a.fromNode.uid!s} to {a.toNode.uid!s}'.format(**locals())
            pdg(G)
            raise KeyError(err_msg)
        if(a.toNode not in G.setOfNodes):
            err_msg = 'There is no Node {a.toNode.uid!s} to match the Arc from {a.fromNode.uid!s} to {a.toNode.uid!s}'.format(**locals())
            pdg(G)
            raise KeyError(err_msg)
        G_as_dict[a.fromNode] = (G_as_dict[a.fromNode].union(frozenset([a]))) if (a.fromNode in G_as_dict) else frozenset([a])
    for a in G.setOfArcs:
        if(a.fromNode not in G.setOfNodes):
            err_msg = 'There is no Node {a.fromNode.uid!s} to match the Arc from {a.fromNode.uid!s} to {a.toNode.uid!s}'.format(**locals())
            raise KeyError(err_msg)
        if a.toNode not in G_as_dict:
            G_as_dict[a.toNode] = frozenset([])
    return G_as_dict

def digraph_to_double_dict(G):
    G_as_dict = dict([])
    for a in G.setOfArcs:
        if(a.fromNode not in G.setOfNodes):
            err_msg = 'There is no Node {a.fromNode.uid!s} to match the Arc from {a.fromNode.uid!s} to {a.toNode.uid!s}'.format(**locals())
            raise KeyError(err_msg)
        if(a.toNode not in G.setOfNodes):
            err_msg = 'There is no Node {a.toNode.uid!s} to match the Arc from {a.fromNode.uid!s} to {a.toNode.uid!s}'.format(**locals())
            raise KeyError(err_msg)
        if(a.fromNode not in G_as_dict):
             G_as_dict[a.fromNode] = dict({a.toNode : frozenset([a])})  
        else:
            if(a.toNode not in G_as_dict[a.fromNode]):
                G_as_dict[a.fromNode][a.toNode] = frozenset([a])
            else:
                G_as_dict[a.fromNode][a.toNode] = G_as_dict[a.fromNode][a.toNode].union(frozenset([a]))

    for a in G.setOfArcs:
        if(a.fromNode not in G.setOfNodes):
            err_msg = 'There is no Node {a.fromNode.uid!s} to match the Arc from {a.fromNode.uid!s} to {a.toNode.uid!s}'.format(**locals())
            raise KeyError(err_msg)
        if a.toNode not in G_as_dict:
            G_as_dict[a.toNode] = dict({})  
    return G_as_dict


def g_dict_to_str(G_dict):
    out_str = ''
    for n in sorted(G_dict.keys()):
        out_str += '{0:>10}: '.format(n.uid) + str([a.toNode.uid for a in G_dict[n]]) + '\n\n'
    return out_str.rstrip()

def agg_n_to_u_cap(n,u,G_as_dict):
    arcs_out = G_as_dict[n]
    return sum([a.datum.capacity for a in arcs_out if( (a.fromNode == n) and (a.toNode == u) ) ])

def agg_n_to_u_flow(n,u,G_as_dict):
    arcs_out = G_as_dict[n]
    return sum([a.datum.flow for a in arcs_out if( (a.fromNode == n) and (a.toNode == u) ) ])

def find_node_by_uid(find_uid, G):
    nodes = {n for n in G.setOfNodes if n.uid == find_uid}
    if(len(nodes) != 1):
        err_msg = 'Node with uid {find_uid!s} is not unique.'.format(**locals())
        raise KeyError(err_msg)
    return nodes.pop()

def get_residual_graph_of(G):
    G_as_dict = digraph_to_dict(G)
    residual_nodes = G.setOfNodes
    residual_arcs = frozenset([])

    for n in G_as_dict:
        arcs_from = G_as_dict[n]
        nodes_to = frozenset([find_node_by_uid(a.toNode.uid,G) for a in arcs_from])

        for u in nodes_to: 
            n_to_u_cap_sum  = agg_n_to_u_cap(n,u,G_as_dict)
            n_to_u_flow_sum = agg_n_to_u_flow(n,u,G_as_dict)
            #print('```',n_to_u_cap_sum,n_to_u_flow_sum )
            if(n_to_u_cap_sum > n_to_u_flow_sum):
                #print('aaaaa')
                flow = round(n_to_u_cap_sum - n_to_u_flow_sum, TOL)
                residual_arcs = residual_arcs.union( frozenset([Arc(n,u,datum=ResidualDatum(flow, 'push'))]) )
            if(n_to_u_flow_sum > 0.0):
                #print('aaaaa')
                flow = round(n_to_u_flow_sum, TOL)
                residual_arcs = residual_arcs.union( frozenset([Arc(u,n,datum=ResidualDatum(flow, 'pull'))]) )
    return DiGraph(residual_nodes, residual_arcs)

def example_2():
    sid, tid = 's', 't'
    s = Node(sid,FlowNodeDatum(0,0))
    t = Node(tid,FlowNodeDatum(0,0))
    a = Node('a',FlowNodeDatum(0,0))
    b = Node('b',FlowNodeDatum(0,0))
    c = Node('c',FlowNodeDatum(0,0))
    d = Node('d',FlowNodeDatum(0,0))
    e = Node('e',FlowNodeDatum(0,0))
    f = Node('f',FlowNodeDatum(0,0))

    sa = Arc(s,a,FlowArcDatum(3.3333,0.0))
    sc = Arc(s,c,FlowArcDatum(6.6666,0.0))
    se = Arc(s,e,FlowArcDatum(8.2518,0.0))

    ab = Arc(a,b,FlowArcDatum(2.2222,0.0))
    ad = Arc(a,d,FlowArcDatum(7.1415,0.0))
    ac = Arc(a,c,FlowArcDatum(4.2222,0.0))

    bt = Arc(b,t,FlowArcDatum(3.1111,0.0))
    bc = Arc(b,c,FlowArcDatum(6.4444,0.0))
    bd = Arc(b,d,FlowArcDatum(1.1111,0.0))

    cb = Arc(c,b,FlowArcDatum(4.1212,0.0))
    cd = Arc(c,d,FlowArcDatum(1.1111,0.0))
    cf = Arc(c,f,FlowArcDatum(2.2222,0.0))

    da = Arc(d,a,FlowArcDatum(2.1121,0.0))
    dt = Arc(d,t,FlowArcDatum(9.1121,0.0))
    df = Arc(d,f,FlowArcDatum(1.4444,0.0))
    dc = Arc(d,c,FlowArcDatum(1.2222,0.0))

    ft  = Arc(f,t,FlowArcDatum(4.1111,0.0))
    ft1 = Arc(f,t,FlowArcDatum(1.1111,0.0))
    ft2 = Arc(f,t,FlowArcDatum(1.1111,0.0))
    ft3 = Arc(f,t,FlowArcDatum(1.1111,0.0))
    ft4 = Arc(f,t,FlowArcDatum(2.1111,0.0))
    fd = Arc(f,d,FlowArcDatum(5.6666,0.0))

    ec = Arc(e,c,FlowArcDatum(4.1111,0.0))
    ef = Arc(e,f,FlowArcDatum(4.3333,0.0))

    nodes = frozenset({s,t,a,b,c,d,e,f})
    arcs  = frozenset({sa,sc,se,ab,ad,ac,bt,bc,bd,cb,cd,cf,dt,df,dc,da,ft,fd,ec,ef,ft1,ft2,ft3,ft4})

    G = strip_flows(DiGraph(nodes, arcs))
    mfps = MaxFlowProblemState(digraph=G, sourceNodeUid=sid, terminalNodeUid=tid, maxFlowProblemStateUid='mathexchange-example')

    result = edmonds_karp(mfps)
    value = get_mfps_flow(result)
    print(value)
    result = fast_edmonds_karp(mfps)
    print(fast_get_mfps_flow(result))
    return value, result

def path_to_str(path):
    return( ['Path[' + a.fromNode.uid + '-->' + a.toNode.uid + ']' for a in path] )

def paint_mfp_path(mfp, iter_count, apath):
    residual_digraph = get_residual_graph_of(mfp.digraph)
    g_dict = digraph_to_dict(mfp.digraph)
    r_dict = digraph_to_dict(residual_digraph)
    gname  = mfp.maxFlowProblemStateUid + '-G:' + str(iter_count).zfill(8) + 'Z'
    rname  = mfp.maxFlowProblemStateUid + '-R:' + str(iter_count).zfill(8) + 'Z' 
    g_dot  = dict_to_dot(g_dict, name='G:'+str(iter_count*2+1))
    r_dot  = dict_to_dot(r_dict, name='R:'+str(iter_count*2+1))
    r_dot  = color_path(apath, G_dot=r_dot, color='red')
    gpath  = apath_to_gset(apath, mfp.digraph)

    if (debug):
        print('>>gpatha', path_to_str(apath))
        print('>>gpath', path_to_str(gpath))

    #g_dot = color_path(gpath, G_dot=g_dot, color='green')
    #A path in the augmented graph may not be a path in the original graph!
    g_dot = color_arcs_nodes(gpath, G_dot=g_dot, color='green')
    dot_to_file(r_dot, name=rname)
    dot_to_file(g_dot, name=gname)

def paint_mfp_graph(mfp, iter_count):
    residual_digraph = get_residual_graph_of(mfp.digraph)
    g_dict = digraph_to_dict(mfp.digraph)
    r_dict = digraph_to_dict(residual_digraph)
    gname = mfp.maxFlowProblemStateUid + '-G:' + str(iter_count).zfill(8) + 'A'
    rname = mfp.maxFlowProblemStateUid + '-R:' + str(iter_count).zfill(8) + 'A'
    g_dot = dict_to_dot(g_dict,name='G:'+str(iter_count*2))
    r_dot = dict_to_dot(r_dict,name='R:'+str(iter_count*2))
    dot_to_file(r_dot, name=rname)
    dot_to_file(g_dot, name=gname)

def source_nodes(G):
    to_nodes = frozenset({a.toNode for a in G.setOfArcs})
    sources = G.setOfNodes.difference(to_nodes)
    return sources

def terminal_nodes(G):
    from_nodes = frozenset({a.fromNode for a in G.setOfArcs})
    terminals = G.setOfNodes.difference(from_nodes)
    return terminals

def cut_predecessors_of(n, cut, G):
    allowed_arcs   = G.setOfArcs.difference(frozenset(cut.setOfCutArcs))
    predecessors   = frozenset({})
    previous_count = len(predecessors)
    reach_fringe   = frozenset({n})
    keep_going     = True
    while( keep_going ):
        reachable_from = frozenset({a.fromNode for a in allowed_arcs if (a.toNode in reach_fringe)})
        reach_fringe   = reachable_from
        predecessors   = predecessors.union(reach_fringe)
        current_count  = len(predecessors) 
        keep_going     = current_count -  previous_count > 0
        previous_count = current_count
    return predecessors

def cut_successors_of(n, cut, G):
    allowed_arcs   = G.setOfArcs.difference(frozenset(cut.setOfCutArcs))
    successors     = frozenset({})
    previous_count = len(successors)
    reach_fringe   = frozenset({n})
    keep_going     = True
    while( keep_going ):
        reachable_from = frozenset({a.toNode for a in allowed_arcs if (a.fromNode in reach_fringe)})
        reach_fringe   = reachable_from
        successors     = successors.union(reach_fringe)
        current_count  = len(successors) 
        keep_going     = current_count -  previous_count > 0
        previous_count = current_count
    return successors

def get_first_part(cut, G):
    firstPartFringe = frozenset({a.fromNode for a in cut.setOfCutArcs})
    firstPart = firstPartFringe
    for n in firstPart:
        preds = cut_predecessors_of(n,cut,G)
        firstPart = firstPart.union(preds)
    return firstPart

def get_second_part(cut, G):
    secondPartFringe = frozenset({a.toNode for a in cut.setOfCutArcs})
    secondPart = secondPartFringe
    for n in secondPart:
        secondPart = secondPart.union(cut_successors_of(n,cut,G))
    return secondPart

def cut_capacity(stCut, G):
    part_1 = get_first_part(stCut.cut,G)
    part_2 = get_second_part(stCut.cut,G)
    s_part = part_1 if stCut.s in part_1 else part_2
    t_part = part_1 if stCut.t in part_1 else part_2
    cut_capacity = sum({a.datum.capacity for a in stCut.cut.setOfCutArcs if ( (a.fromNode in s_part) and (a.toNode in t_part) )})
    return cut_capacity

ArcMatchingDatum = coll.namedtuple('ArcMatchingDatum', ['inMatching' ])
NodeMatchingDatum = coll.namedtuple('NodeMatchingDatum', ['visited'])

def dfs_helper(snodes, G):
    sniter, do_stop = iter(snodes), False
    visited, visited_uids = set(), set()
    while(not do_stop):
        try:
            stack = [ next(sniter) ]
            while len(stack) > 0:
                curr = stack.pop()
                #print('Visit', curr.uid, len(snodes))
                if curr.uid not in visited_uids:
                    visited = visited.union( frozenset( {Node(curr.uid, NodeMatchingDatum(False))} ) )
                    visited_uids = visited.union(frozenset({curr.uid}))
                    succ = frozenset({a.toNode for a in G.setOfArcs if a.fromNode == curr})
                    stack.extend( succ.difference( frozenset(visited) ) )
        except StopIteration as e:
            stack, do_stop = [], True
    return visited

def get_min_node_cover(matching, bipartition):
    nodes = frozenset( { Node(n.uid, NodeMatchingDatum(False)) for n in bipartition.digraph.setOfNodes} ) 
    G = DiGraph(nodes, None)
    charcs = frozenset( {a for a in matching if ( (a.fromNode in bipartition.firstPart) and (a.toNode in bipartition.secondPart) )} )
    arcs0 = frozenset( { Arc(find_node_by_uid(a.toNode.uid,G), find_node_by_uid(a.fromNode.uid,G), ArcMatchingDatum(True) ) for a in charcs } )
    arcs1 = frozenset( { Arc(find_node_by_uid(a.fromNode.uid,G), find_node_by_uid(a.toNode.uid,G), ArcMatchingDatum(True) ) for a in matching.difference(charcs) } )
    not_matching = bipartition.digraph.setOfArcs.difference( matching )
    charcs = frozenset( {a for a in not_matching if ( (a.fromNode in bipartition.secondPart) and (a.toNode in bipartition.firstPart) )} )
    arcs2 = frozenset( { Arc(find_node_by_uid(a.toNode.uid,G), find_node_by_uid(a.fromNode.uid,G), ArcMatchingDatum(False) ) for a in charcs } )
    arcs3 = frozenset( { Arc(find_node_by_uid(a.fromNode.uid,G), find_node_by_uid(a.toNode.uid,G), ArcMatchingDatum(False) ) for a in not_matching.difference(charcs) } )
    arcs = arcs0.union(arcs1.union(arcs2.union(arcs3)))
    
    G = DiGraph(nodes, arcs)
    bip = Bipartition({find_node_by_uid(n.uid,G) for n in bipartition.firstPart},{find_node_by_uid(n.uid,G) for n in bipartition.secondPart},G)
    match_from_nodes = frozenset({find_node_by_uid(a.fromNode.uid,G) for a in matching}) 
    match_to_nodes = frozenset({find_node_by_uid(a.toNode.uid,G) for a in matching})
    snodes = bip.firstPart.difference(match_from_nodes).difference(match_to_nodes)
    visited_nodes = dfs_helper(snodes, bip.digraph)
    not_visited_nodes = bip.digraph.setOfNodes.difference(visited_nodes)

    H = DiGraph(visited_nodes.union(not_visited_nodes), arcs)
    cover1 = frozenset( {a.fromNode for a in H.setOfArcs if ( (a.datum.inMatching) and (a.fromNode.datum.visited) ) } ) 
    cover2 = frozenset( {a.fromNode for a in H.setOfArcs if ( (a.datum.inMatching) and (not a.toNode.datum.visited) ) } )
    min_cover_nodes = cover1.union(cover2)
    true_min_cover_nodes = frozenset({find_node_by_uid(n.uid, bipartition.digraph) for n in min_cover_nodes})
    #print('Matching', {(x.fromNode.uid,x.toNode.uid) for x in matching})
    #print('Min Cover', {x.uid for x in true_min_cover_nodes})
 
    return min_cover_nodes

WeightArcDatum = coll.namedtuple('WeightArcDatum', ['weight'])
def kuhn_munkres( bip ):
    nodes = bip.digraph.setOfNodes
    arcs = frozenset({})
    original_weights = dict({})

    for a in bip.digraph.setOfArcs:
        original_weights[a.fromNode.uid,a.toNode.uid] = a.datum.weight

    for n in bip.firstPart:
        z = min( {x.datum.weight for x in bip.digraph.setOfArcs if ( (x.fromNode == n) or (x.toNode == n) )} )
        arcs = arcs.union( frozenset({Arc(a.fromNode, a.toNode, WeightArcDatum(a.datum.weight - z))
                                      for a in bip.digraph.setOfArcs 
                                      if ( (a.fromNode == n) or (a.toNode == n) )}) )
    for n in bip.secondPart:
        z = min( {x.datum.weight for x in bip.digraph.setOfArcs if ( (x.fromNode == n) or (x.toNode == n) )} )
        arcs = arcs.union( frozenset({Arc(a.fromNode, a.toNode, WeightArcDatum(a.datum.weight - z))
                                      for a in bip.digraph.setOfArcs 
                                      if ( (a.fromNode == n) or (a.toNode == n) )}) )

    for a in arcs:
        print('{!s:15}{!s:15}{!s:15}'.format(a.fromNode.uid, a.toNode.uid, a.datum.weight))


    H = DiGraph(nodes, arcs)
    assignment, value, not_done = dict({}), 0, True

    while( not_done ):
        print('Bob', '----')
        for a in H.setOfArcs:
            print('{!s:15}{!s:15}{!s:15}'.format(a.fromNode.uid, a.toNode.uid, a.datum.weight))

        zwarcs = frozenset( {a for a in H.setOfArcs if a.datum.weight == 0} )
        znodes = frozenset( {n.fromNode for n in zwarcs} ).union( frozenset( {n.toNode for n in zwarcs} ) )
        K = DiGraph(znodes, zwarcs)    
        k_bipartition = bipartition(K)
        matching = solve_mbm( k_bipartition )
        mnodes = frozenset({a.fromNode for a in matching}).union(frozenset({a.toNode for a in matching}))
        if( len(mnodes) == len(H.setOfNodes) ):
            for a in matching:
                assignment[ a.fromNode.uid ] = a.toNode.uid
                value += original_weights[a.fromNode.uid,a.toNode.uid]
            not_done = False
        else:
            node_cover = get_min_node_cover(matching, bipartition(K))
            z = min( frozenset( {a.datum.weight for a in H.setOfArcs if a not in node_cover} ) )
            arcs1 = frozenset( {Arc(a.fromNode,a.toNode,WeightArcDatum(a.datum.weight-z))
                                for a in H.setOfArcs 
                                if ( (a.fromNode not in node_cover) and (a.toNode not in node_cover))} )
            arcs2 = frozenset( {Arc(a.fromNode,a.toNode,WeightArcDatum(a.datum.weight)) 
                                for a in H.setOfArcs 
                                if ( (a.fromNode not in node_cover) != (a.toNode not in node_cover))} ) 
            arcs3 = frozenset( {Arc(a.fromNode,a.toNode,ArcWeightDatum(a.datum.weigh+z)) 
                                for a in H.setOfArcs 
                                if ( (a.fromNode in node_cover) and (a.toNode in node_cover))} ) 
            nodes = H.setOfNodes
            arcs = arcs1.union(arcs2.union(arcs3))
            H = DiGraph(nodes,arcs) 
            print('X')
            sys.exit(1)

    ndz = {a.fromNode for a in matching}.union({a.toNode for a in matching})
    acz = {Arc(a.fromNode, a.toNode, WeightArcDatum(original_weights[a.fromNode.uid, a.toNode.uid])) for a in matching}
    X = DiGraph(ndz, acz) 
    for a in X.setOfArcs:
        print(a)
    g_dict = digraph_to_dict(X)
    g_dot = dict_to_dot(g_dict)
    dot_to_file(g_dot,name='assign')
    print(value, assignment)
    return value, assignment

def example_5():
    a = Node('Alice',FlowNodeDatum(0,0))
    b = Node('Bob',FlowNodeDatum(0,0))
    c = Node('Charlie',FlowNodeDatum(0,0))
    d = Node('Diane',FlowNodeDatum(0,0))
    x1 = Node('Bathroom',FlowNodeDatum(0,0))
    x2 = Node('Floor',FlowNodeDatum(0,0))
    x3 = Node('Windows',FlowNodeDatum(0,0))
    x4 = Node('Nothing',FlowNodeDatum(0,0))

    a1 = Arc(a,x1,WeightArcDatum(2))
    a2 = Arc(a,x2,WeightArcDatum(3))
    a3 = Arc(a,x3,WeightArcDatum(3))
    a4 = Arc(a,x4,WeightArcDatum(0))
    b1 = Arc(b,x1,WeightArcDatum(3))
    b2 = Arc(b,x2,WeightArcDatum(2))
    b3 = Arc(b,x3,WeightArcDatum(3))
    b4 = Arc(b,x4,WeightArcDatum(0))
    c1 = Arc(c,x1,WeightArcDatum(3))
    c2 = Arc(c,x2,WeightArcDatum(3))
    c3 = Arc(c,x3,WeightArcDatum(2))
    c4 = Arc(c,x4,WeightArcDatum(0))
    d1 = Arc(d,x1,WeightArcDatum(9))
    d2 = Arc(d,x2,WeightArcDatum(9))
    d3 = Arc(d,x3,WeightArcDatum(1))
    d4 = Arc(d,x4,WeightArcDatum(0))

    nodes = {a,b,c,d,x1,x2,x3,x4}
    arcs = {a1,a2,a3,a4,b1,b2,b3,b4,c1,c2,c3,c4,d1,d2,d3,d4}
    G = DiGraph(nodes, arcs)
    bip = bipartition(G) 
    print( 'First-Part', {x.uid for x in bip.firstPart} )
    print( 'Second-Part', {x.uid for x in bip.secondPart} )
    kuhn_munkres( bip )   
    import sys; sys.exit(1)


def example_4():
    a = Node('a',FlowNodeDatum(0,0))
    b = Node('b',FlowNodeDatum(0,0))
    c = Node('c',FlowNodeDatum(0,0))
    d = Node('d',FlowNodeDatum(0,0))
    x1 = Node('1',FlowNodeDatum(0,0))
    x2 = Node('2',FlowNodeDatum(0,0))
    x3 = Node('3',FlowNodeDatum(0,0))
    x4 = Node('4',FlowNodeDatum(0,0))
    a1 = Arc(a,x1,WeightArcDatum(-5))
    a2 = Arc(a,x2,WeightArcDatum(1))
    a3 = Arc(a,x3,WeightArcDatum(1))
    b1 = Arc(b,x1,WeightArcDatum(1))
    b3 = Arc(b,x3,WeightArcDatum(1))
    c2 = Arc(c,x2,WeightArcDatum(1))
    d2 = Arc(d,x2,WeightArcDatum(1))
    d3 = Arc(d,x3,WeightArcDatum(1))
    d4 = Arc(d,x4,WeightArcDatum(1))
    nodes = {a,b,c,d,x1,x2,x3,x4}
    arcs = {a1,a2,a3,b1,b3,c2,d2,d3,d4}
    G = DiGraph(nodes, arcs)
    bip = bipartition(G) 
    print( 'First-Part', {x.uid for x in bip.firstPart} )
    print( 'Second-Part', {x.uid for x in bip.secondPart} )
    kuhn_munkres( bip )   
    import sys; sys.exit(1)

def example_3():
    a = Node('a',FlowNodeDatum(0,0))
    b = Node('b',FlowNodeDatum(0,0))
    c = Node('c',FlowNodeDatum(0,0))
    d = Node('d',FlowNodeDatum(0,0))
    x1 = Node('1',FlowNodeDatum(0,0))
    x2 = Node('2',FlowNodeDatum(0,0))
    x3 = Node('3',FlowNodeDatum(0,0))
    a1 = Arc(a,x1,FlowArcDatum(1,0))
    a2 = Arc(a,x2,FlowArcDatum(1,0))
    a3 = Arc(a,x3,FlowArcDatum(1,0))
    x1b= Arc(x1,b,FlowArcDatum(1,0))
    b3 = Arc(b,x3,FlowArcDatum(1,0))
    c2 = Arc(c,x2,FlowArcDatum(1,0))
    d2 = Arc(d,x2,FlowArcDatum(1,0))
    d3 = Arc(d,x3,FlowArcDatum(1,0))
    nodes = {a,b,c,d,x1,x2,x3}
    arcs = {a1,a2,a3,x1b,b3,c2,d2,d3}
    G = DiGraph(nodes, arcs)
    bip = bipartition(G) 
    print( 'First-Part', {x.uid for x in bip.firstPart} )
    print( 'Second-Part', {x.uid for x in bip.secondPart} )
    matching = solve_mbm(bip)
    for a in matching:
        print((a.fromNode.uid,a.toNode.uid))

    get_min_node_cover(matching, bip)
        
    import sys; sys.exit(1)

def example_1():
    s = Node('s',FlowNodeDatum(0,0))
    a = Node('a',FlowNodeDatum(0,0))
    b = Node('b',FlowNodeDatum(0,0))
    c = Node('c',FlowNodeDatum(0,0))
    d = Node('d',FlowNodeDatum(0,0))
    t = Node('t',FlowNodeDatum(0,0))
    
    sa = Arc(s,a,FlowArcDatum(3,0))
    sd = Arc(s,d,FlowArcDatum(3,0))
    ab = Arc(a,b,FlowArcDatum(2,0))
    ad = Arc(a,d,FlowArcDatum(2,0))
    bc = Arc(b,c,FlowArcDatum(4,0))
    bt = Arc(b,t,FlowArcDatum(2,0))
    ct = Arc(c,t,FlowArcDatum(2,0))
    dc = Arc(d,c,FlowArcDatum(3,0))
    
    sid = 's'
    tid = 't' 
    nodes = frozenset([s,a,b,c,d,t])
    arcs  = frozenset([sa,sd,ab,ad,bc,bt,ct,dc])

    #G = strip_flows(DiGraph(nodes, arcs))
    G = DiGraph(nodes, arcs)
    print('Sources', [n.uid for n in source_nodes(G)] )
    print('Terminals', [n.uid for n in terminal_nodes(G)] )
    cut = Cut({ab, dc})
    predz = cut_predecessors_of(find_node_by_uid('a',G),cut,G)
    succz = cut_successors_of(find_node_by_uid('a',G),cut,G)
    print('Preds of ', a.uid, [n.uid for n in predz] )
    print('Succs of ', a.uid,  [n.uid for n in succz] )
    part_1 = get_first_part(cut,G)
    part_2 = get_second_part(cut,G)
    print('Part 1', [n.uid for n in part_1] )
    print('Part 2', [n.uid for n in part_2] )
    stcut = STCut(s,t,cut)
    cc = cut_capacity(stcut,G) 
    print('Cut Cap', cc )
    example_3()

    
    mfps = MaxFlowProblemState(digraph=G, sourceNodeUid=sid, terminalNodeUid=tid, maxFlowProblemStateUid='wiki-FF-example')

    result = edmonds_karp(mfps)
    value = get_mfps_flow(result)
    print(value)
    result = fast_edmonds_karp(mfps)
    print(fast_get_mfps_flow(result))

    return value, result

def path_arcs_to_nodes(sarcs):
    snodes = list([])
    arc_it = iter(sarcs)
    step_count = 0
    last = None
    try:
        at_end = False
        last = a1 = next(arc_it)
        while (not at_end):
            snodes += [a1.fromNode]
            last = a2 = next(arc_it)
            step_count += 1
            if(a1.toNode != a2.fromNode):
                ptostr = path_to_str(sarcs)
                err_msg = "Error at index {step_count!s} of Arc sequence: {ptostr!s}".format(**locals())
                raise ValueError(err_msg)
            a1 = a2
    except StopIteration as e:
        at_end = True
        
    if(last is not None):
        snodes += [last.toNode]

    return snodes

def arcs_to_nodes(sarcs):
    snodes = list([])
    arc_it = iter(sarcs)
    step_count = 0
    last = None
    try:
        at_end = False
        last = a1 = next(arc_it)
        while (not at_end):
            snodes += [a1.fromNode]
            last = a2 = next(arc_it)
            step_count += 1
            a1 = a2
    except StopIteration as e:
        at_end = True
        
    if(last is not None):
        snodes += [last.toNode]

    return snodes


'''
https://www.python.org/doc/essays/graphs/
http://www.graphviz.org/doc/info/lang.html
http://pygraphviz.github.io/documentation/latest/pygraphviz.pdf
'''
def dict_to_dot(dict_G, name=''):
    dict_G    = dict(dict_G)
    name      = str(name)

    nodes = dict_G.keys()
    G = pgv.AGraph(name=name, label=name, strict=False, directed=True, rankdir="LR")
    
    x_dim, y_dim         = 0.1, 0.1
    tail,adir,ahlen      = 'dot','both',0.62
    arc_descriptor_shape = 'plain'
    node_shape           = 'egg'
    arc_shape            = 'plain'
    arc_arrow_head       = 'normal'
    arc_arrow_tail       = 'dot'
    arc_mid              = 'none'
    arc_dir              = 'both'
    
    for node in nodes:
        G.add_node(node.uid,label=node_to_label(node))
        arcs = dict_G[node]
        for arc in arcs:
            arc_id = arc_to_id(arc)
            G.add_node(arc_id,shape=arc_descriptor_shape,label=arc_to_label(arc),width=x_dim,height=y_dim)
            G.add_edge(node.uid,arc_id,len=ahlen,dir=arc_dir,arrowtail=arc_arrow_tail,arrowhead=arc_mid)
            G.add_edge(arc_id,arc.toNode.uid,shape=arc_shape,arrowtail=arc_mid,arrowhead=arc_arrow_head)
    return G

def dot_to_file(dot_G, name='out', env='./env'):
    G           = dot_G.copy()
    env         = os.path.abspath(env)
    env_dot     = os.path.join(env,'dot')
    env_img     = os.path.join(env,'img')
    layout_prog = 'dot'
    dot_suffix  = 'dot'
    img_suffix  = 'png'

    dot_G.graph_attr.update(name = name)
    dot_G.graph_attr.update(label = name)

    if (debug):
        # print to screen
        print(G.string()) 
    
    if not os.path.exists(env_dot):
        os.makedirs(env_dot)
    if not os.path.exists(env_img):
        os.makedirs(env_img)

    G.layout(prog=layout_prog)
    dot_fname = os.path.join(env_dot, name +'.' + str(dot_suffix))
    img_fname = os.path.join(env_img, name + '.' + str(img_suffix))
    G.write(dot_fname)
    if (debug):
        print("Wrote " + str(dot_fname))

    # create a new graph from file
    G = pgv.AGraph(dot_fname)  
    G.layout(prog=layout_prog)
    G.draw(img_fname)       
    if(debug):
        print("Wrote " + str(img_fname))

def test_3():
    g_dict = example_2()

def test_2():
    g_dict, g_path, nodes, arcs = example_gdict_1()
    g_dot       = dict_to_dot(g_dict)
    dot_to_file(g_dot,name='a1')
 
def test_1():
    G = example_gdict_1()
    g_dict = digraph_to_dict(G)
    g_dot = dict_to_dot(g_dict)

    dot_to_file(g_dot,name='1')
    dot_to_file(color_pathz,name='2')
    dot_to_file(color_nodez,name='3')
    dot_to_file(color_arcz,name='4')

    g_dict = example_gdict()
    g_dot  = dict_to_dot(g_dict)
    dot_to_file(g_dot,name='ABC')

    g_dict = example_house()
    g_dot  = dict_to_dot(g_dict)
    dot_to_file(g_dot,name='house')

def strip_flows(G):
    new_nodes= frozenset( (Node(n.uid, FlowNodeDatum(0.0,0.0)) for n in G.setOfNodes) )
    new_arcs = frozenset([])
    for a in G.setOfArcs:
        new_fromNode = Node(a.fromNode.uid, FlowNodeDatum(0.0,0.0)) 
        new_toNode   = Node(a.toNode.uid, FlowNodeDatum(0.0,0.0)) 
        new_arc      = Arc(new_fromNode, new_toNode, FlowArcDatum(a.datum.capacity, 0.0))
        new_arcs     = new_arcs.union(frozenset([new_arc]))
    return DiGraph(new_nodes, new_arcs)

def bfs(sourceNode, terminalNode, G_f):
    G_f_as_dict = digraph_to_dict(G_f)
    parent_arcs = dict([])
    visited     = frozenset([])
    deq         = coll.deque([sourceNode])
    while len(deq) > 0:
        curr = deq.popleft()
        if curr == terminalNode:
            break
        for a in G_f_as_dict.get(curr):
            if (a.toNode not in visited):
                visited = visited.union(frozenset([a.toNode]))
                parent_arcs[a.toNode] = a
                deq.extend([a.toNode])
    path = list([])
    curr = terminalNode
    while(curr != sourceNode):
        if (curr not in parent_arcs):
            err_msg = 'No augmenting path from {} to {}.'.format(sourceNode.uid, terminalNode.uid)
            raise StopIteration(err_msg)
        path.extend([parent_arcs[curr]])
        curr = parent_arcs[curr].fromNode
    path.reverse()

    test = coll.deque([path[0].fromNode])
    for a in path:
        if(test[-1] != a.fromNode):
            err_msg = 'Bad path: {}'.format(path)
            raise ValueError(err_msg)
        test.extend([a.toNode])
        
    return path

def edmonds_karp(mfp):
    sid, tid = mfp.sourceNodeUid, mfp.terminalNodeUid
    no_more_paths = False
    loop_count = 0
    while(not no_more_paths):
       residual_digraph = get_residual_graph_of(mfp.digraph)
       paint_mfp_graph(mfp, loop_count)
       try:
           asource = find_node_by_uid(mfp.sourceNodeUid, residual_digraph)
           aterm   = find_node_by_uid(mfp.terminalNodeUid, residual_digraph)
           apath   = bfs(asource, aterm, residual_digraph)
           paint_mfp_path(mfp, loop_count, apath)
           G = augment(apath, mfp.digraph)
           s = find_node_by_uid(sid, G)
           t = find_node_by_uid(tid, G)
           mfp = MaxFlowProblemState(digraph=G, sourceNodeUid=s.uid, terminalNodeUid=t.uid, maxFlowProblemStateUid=mfp.maxFlowProblemStateUid)
           loop_count += 1
       except StopIteration as e:
           no_more_paths = True
    return mfp

def apath_to_gset(apath, G):
    G_as_dict = digraph_to_dict(G)
    gpath     = list([])
    for a in apath:
        if (a.datum.action == 'push'):
            from_node_uid = a.fromNode.uid #if a.datum.action == 'push' else a.toNode.uid
            to_node_uid   = a.toNode.uid   #if a.datum.action == 'push' else a.fromNode.uid
            from_node     = find_node_by_uid( from_node_uid, G )
            to_node       = find_node_by_uid( to_node_uid, G )
            old_len       = len(gpath)
            for a in G_as_dict[from_node]:
                if(a.toNode == to_node):
                    gpath += [a]
            #if(old_len +1 != len(gpath)):
            #    err_msg = 'No Arc from {from_node.uid!s} to {to_node.uid!s}.'.format(**locals())
            #    raise KeyError(err_msg)
        #else:
            #pass
            #prev_arc     = gpath[-1]
            #prev_to_node = find_node_by_uid( prev_arc.toNode.uid, G ) 
            #nxt_to_node  = find_node_by_uid( a.toNode.uid, G        )
            #p_to_n_arc_max = max( {a1 for a1 in G_as_dict[prev_to_node] if a1.toNode == nxt_to_node}, key=lambda x: (x.datum.capacity - x.datum.flow) )
            #gpath.pop()
            #gpath += [p_to_n_arc_max] 


    #test = coll.deque([gpath[0].fromNode])
    #for a in gpath:
    #    if(test[-1] != a.fromNode):
    #        print(apath)
    #        err_msg = 'Bad path: {}'.format( path_to_str(gpath) )
    #        raise ValueError(err_msg)
    #    test.extend([a.toNode])
    return gpath

def get_mfps_flow(mfps):
    flow_from_s = find_node_by_uid(mfps.sourceNodeUid,mfps.digraph).datum.flowOut
    flow_to_t   = find_node_by_uid(mfps.terminalNodeUid,mfps.digraph).datum.flowIn

    if( (flow_to_t - flow_from_s) > 0.00):
        print(flow_from_s, flow_to_t)
        raise Exception('Infeasible s-t flow')
    return flow_to_t

    #return sum(a.datum.flow for a in mfps.digraph.setOfArcs if(a.toNode.uid == mfps.terminalNodeUid) )

def fast_get_mfps_flow(mfps):
    flow_from_s = {n for n in mfps.digraph.setOfNodes if n.uid == mfps.sourceNodeUid}.pop().datum.flowOut
    flow_to_t   = {n for n in mfps.digraph.setOfNodes if n.uid == mfps.terminalNodeUid}.pop().datum.flowIn

    #print('FF', flow_from_s, flow_to_t)
    if( (flow_to_t - flow_from_s) > 0.00):
        raise Exception('Infeasible s-t flow')
    return flow_to_t


    #return sum(a.datum.flow for a in mfps.digraph.setOfArcs if(a.toNode == mfps.terminalNodeUid) )

def augment(augmentingPath, H):
    augmentingPath = list(augmentingPath)
    H_as_dict      = digraph_to_dict(H)
    new_nodes      = frozenset({})
    new_arcs       = frozenset({})
    visited_nodes  = frozenset({})
    visited_arcs   = frozenset({})

    bottleneck_residualCapacity = min( augmentingPath, key=lambda a: a.datum.residualCapacity ).datum.residualCapacity
    for x in augmentingPath:
        from_node_uid = x.fromNode.uid if x.datum.action == 'push' else x.toNode.uid
        to_node_uid   = x.toNode.uid   if x.datum.action == 'push' else x.fromNode.uid
        from_node     = find_node_by_uid( from_node_uid, H )
        to_node       = find_node_by_uid( to_node_uid, H )
        load          = bottleneck_residualCapacity if x.datum.action == 'push' else -bottleneck_residualCapacity

        for a in H_as_dict[from_node]:
            if(a.toNode == to_node):
                test_sum = a.datum.flow + load
                new_flow = a.datum.flow
                new_from_node_flow_out = a.fromNode.datum.flowOut
                new_to_node_flow_in = a.toNode.datum.flowIn

                new_from_look = {n for n in new_nodes if (n.uid == a.fromNode.uid)}
                new_to_look   = {n for n in new_nodes if (n.uid == a.toNode.uid)  }
                prev_from_node= new_from_look.pop() if (len(new_from_look)>0) else a.fromNode
                prev_to_node  = new_to_look.pop()   if (len(new_to_look)>0)   else a.toNode
                new_nodes = new_nodes.difference(frozenset({prev_from_node}))
                new_nodes = new_nodes.difference(frozenset({prev_to_node}))

                if(test_sum > a.datum.capacity):
                    new_flow = a.datum.capacity
                    new_from_node_flow_out = prev_from_node.datum.flowOut - a.datum.flow + a.datum.capacity
                    new_to_node_flow_in    = prev_to_node.datum.flowIn - a.datum.flow + a.datum.capacity
                    load = test_sum - a.datum.capacity
                    if(debug):
                        print('zzzaaa', from_node.uid, to_node.uid, new_from_node_flow_out, new_to_node_flow_in)
                elif(test_sum < 0.0):
                    new_flow = 0.0
                    new_from_node_flow_out = prev_from_node.datum.flowOut - a.datum.flow
                    new_to_node_flow_in    = prev_to_node.datum.flowIn - a.datum.flow
                    load = test_sum
                    if(debug):
                        print('1zzzaaa', from_node.uid, to_node.uid, new_from_node_flow_out, new_to_node_flow_in)
                else:
                    new_flow = test_sum
                    new_from_node_flow_out = prev_from_node.datum.flowOut - a.datum.flow + new_flow
                    new_to_node_flow_in    = prev_to_node.datum.flowIn - a.datum.flow + new_flow
                    load = 0.0
                    if(debug):
                        print('2zzzaaa', from_node.uid, to_node.uid, new_from_node_flow_out, new_to_node_flow_in)

                new_from_node_flow_out = round(new_from_node_flow_out, TOL)
                new_to_node_flow_in    = round(new_to_node_flow_in, TOL)
                new_flow               = round(new_flow, TOL)

                new_from_node = Node(prev_from_node.uid, FlowNodeDatum(prev_from_node.datum.flowIn, new_from_node_flow_out))
                new_to_node   = Node(prev_to_node.uid, FlowNodeDatum(new_to_node_flow_in, prev_to_node.datum.flowOut))
                new_arc       = Arc(new_from_node, new_to_node, FlowArcDatum(a.datum.capacity, new_flow))

                #print('nfn', new_from_node)
                #print('ntn', new_to_node)
                #print('nark', new_arc)

                visited_nodes = visited_nodes.union(frozenset({a.fromNode,a.toNode}))
                visited_arcs  = visited_arcs.union(frozenset({a}))
                new_nodes     = new_nodes.union(frozenset({new_from_node, new_to_node}))
                new_arcs      = new_arcs.union(frozenset({new_arc}))

    not_visited_nodes = H.setOfNodes.difference(visited_nodes)
    not_visited_arcs  = H.setOfArcs.difference(visited_arcs)

    #new_nodes = set([a.fromNode for a in new_arcs]).union(set([a.toNode for a in new_arcs])).union(not_visited_nodes)
    full_new_nodes = new_nodes.union(not_visited_nodes)
    full_new_arcs  = new_arcs.union(not_visited_arcs)
    G = DiGraph(full_new_nodes, full_new_arcs)

    full_new_arcs_update = frozenset([])
    for a in full_new_arcs:        
        new_from_node = a.fromNode
        new_to_node   = a.toNode
        new_from_node = find_node_by_uid( a.fromNode.uid, G )
        new_to_node   = find_node_by_uid( a.toNode.uid, G )
        full_new_arcs_update = full_new_arcs_update.union( {Arc(new_from_node, new_to_node, FlowArcDatum(a.datum.capacity, a.datum.flow))} )

    G = DiGraph(full_new_nodes, full_new_arcs_update)
    pdg(G)

    return G

def fast_e_k_preprocess(G):
    G                            = strip_flows(G)
    get                          = dict({})
    get['nodes']                 = dict({})
    get['node_to_node_capacity'] = dict({})
    get['node_to_node_flow']     = dict({})
    get['arcs']                  = dict({})
    get['residual_arcs']         = dict({})

    for a in G.setOfArcs:
        if(a.fromNode not in G.setOfNodes):
            err_msg = 'There is no Node {a.fromNode.uid!s} to match the Arc from {a.fromNode.uid!s} to {a.toNode.uid!s}'.format(**locals())
            raise KeyError(err_msg)
        if(a.toNode not in G.setOfNodes):
            err_msg = 'There is no Node {a.toNode.uid!s} to match the Arc from {a.fromNode.uid!s} to {a.toNode.uid!s}'.format(**locals())
            raise KeyError(err_msg)
        get['nodes'][a.fromNode.uid] = a.fromNode  
        get['nodes'][a.toNode.uid]   = a.toNode  
        lark = Arc(a.fromNode.uid, a.toNode.uid, FlowArcDatumWithUid(a.datum.capacity, a.datum.flow, uuid.uuid4()))
        if(a.fromNode.uid not in get['arcs']):
            get['arcs'][a.fromNode.uid] = dict({a.toNode.uid : dict({lark.datum.uid : lark})})  
        else:
            if(a.toNode.uid not in get['arcs'][a.fromNode.uid]):
                get['arcs'][a.fromNode.uid][a.toNode.uid] = dict({lark.datum.uid : lark})
            else:
                get['arcs'][a.fromNode.uid][a.toNode.uid][lark.datum.uid] = lark

    for a in G.setOfArcs:
        if a.toNode.uid not in get['arcs']:
            get['arcs'][a.toNode.uid] = dict({})  
 
    for n in get['nodes']:
        get['residual_arcs'][n]         = dict()
        get['node_to_node_capacity'][n] = dict()
        get['node_to_node_flow'][n]     = dict()
        for u in get['nodes']:
            n_to_u_cap_sum  = sum(a.datum.capacity for a in G.setOfArcs if (a.fromNode.uid == n) and (a.toNode.uid == u) )
            n_to_u_flow_sum = sum(a.datum.flow     for a in G.setOfArcs if (a.fromNode.uid == n) and (a.toNode.uid == u) )

            if(n_to_u_cap_sum > n_to_u_flow_sum):
                flow = round(n_to_u_cap_sum - n_to_u_flow_sum, TOL)
                get['residual_arcs'][n][u] = Arc(n,u,ResidualDatum(flow, 'push'))
            if(n_to_u_flow_sum > 0.0):
                flow = round(n_to_u_flow_sum, TOL)
                get['residual_arcs'][u][n] = Arc(u,n,ResidualDatum(flow, 'pull'))

            get['node_to_node_capacity'][n][u] = n_to_u_cap_sum
            get['node_to_node_flow'][n][u]     = n_to_u_flow_sum

    return get

def fast_bfs(sid, tid, get):
    parent_of   = dict([])
    visited     = frozenset([])
    deq         = coll.deque([sid])
    while len(deq) > 0:
        n = deq.popleft()
        if n == tid:
            break
        for u in get['residual_arcs'][n]:
            if (u not in visited):
                visited = visited.union(frozenset({u}))
                parent_of[u] = get['residual_arcs'][n][u]
                deq.extend([u])
    path = list([])
    curr = tid
    while(curr != sid):
        if (curr not in parent_of):
            err_msg = 'No augmenting path from {} to {}.'.format(sid, curr)
            #print(err_msg)
            raise StopIteration(err_msg)
        path.extend([parent_of[curr]])
        curr = parent_of[curr].fromNode
        #print('EK2',[(x.fromNode, x.toNode) for x in path])
    path.reverse()
        
    return path

def fast_edmonds_karp(mfps):
    sid, tid = mfps.sourceNodeUid, mfps.terminalNodeUid
    get = fast_e_k_preprocess(mfps.digraph)
    no_more_paths, loop_count = False, 0
    while(not no_more_paths):
       #residual_digraph = get_residual_graph_of(mfp.digraph)
       #paint_mfp_graph(mfp, loop_count)
       try:
           #asource = find_node_by_uid(mfp.sourceNodeUid, residual_digraph)
           #aterm   = find_node_by_uid(mfp.terminalNodeUid, residual_digraph)
           #apath   = bfs(asource, aterm, residual_digraph)
           apath   = fast_bfs(sid, tid, get)
           #print([(a.fromNode, a.toNode) for a in apath])
           #paint_mfp_path(mfp, loop_count, apath)
           get = fast_augment(apath, get)
           #s = find_node_by_uid(sid, G)
           #t = find_node_by_uid(tid, G)
           #mfp = MaxFlowProblemState(digraph=G, sourceNodeUid=s.uid, terminalNodeUid=t.uid, maxFlowProblemStateUid=mfp.maxFlowProblemStateUid)
           loop_count += 1
       except StopIteration as e:
           no_more_paths = True
    nodes = frozenset(get['nodes'].values())
    arcs  = frozenset({})
    for from_node in get['arcs']:
        for to_node in get['arcs'][from_node]:
            for arc in get['arcs'][from_node][to_node]:
                arcs |= frozenset({get['arcs'][from_node][to_node][arc]})

    G = DiGraph(nodes, arcs)
    mfps = MaxFlowProblemState(digraph=G, sourceNodeUid=sid, terminalNodeUid=tid, maxFlowProblemStateUid=mfps.maxFlowProblemStateUid)
    return mfps

def fast_augment(augmentingPath, get):
    augmentingPath = list(augmentingPath)

    bottleneck_residualCapacity = min(augmentingPath, key=lambda a: a.datum.residualCapacity).datum.residualCapacity
    for x in augmentingPath:
        from_node_uid = x.fromNode if x.datum.action == 'push' else x.toNode
        to_node_uid   = x.toNode   if x.datum.action == 'push' else x.fromNode
        from_node     = get['nodes'][from_node_uid]
        to_node       = get['nodes'][to_node_uid  ]
        load          = bottleneck_residualCapacity if x.datum.action == 'push' else -bottleneck_residualCapacity

        for a_uid in get['arcs'][from_node_uid][to_node_uid]:
            a = get['arcs'][from_node_uid][to_node_uid][a_uid]
            test_sum = a.datum.flow + load
            new_flow = a.datum.flow
            delta = 0.0

            if(test_sum > a.datum.capacity):
                new_flow = a.datum.capacity
                delta = a.datum.capacity - a.datum.flow
                load = test_sum - a.datum.capacity
            elif(test_sum < 0.0):
                new_flow = 0.0
                delta = -a.datum.flow
                load = test_sum
            else:
                new_flow = test_sum
                delta = new_flow - a.datum.flow
                load = 0.0

            prev_from_node_flow_in = round(get['nodes'][from_node_uid].datum.flowIn, TOL)
            prev_to_node_flow_out  = round(get['nodes'][to_node_uid].datum.flowOut, TOL)
            new_from_node_flow_out = round(get['nodes'][from_node_uid].datum.flowOut + delta, TOL)
            new_to_node_flow_in    = round(get['nodes'][to_node_uid].datum.flowIn + delta, TOL)
            new_flow               = round(new_flow, TOL)

            get['node_to_node_flow'][from_node_uid][to_node_uid] = round(get['node_to_node_flow'][from_node_uid][to_node_uid] + delta, TOL) 
            get['nodes'][from_node_uid] = Node(from_node_uid, FlowNodeDatum(prev_from_node_flow_in, new_from_node_flow_out))
            get['nodes'][to_node_uid  ] = Node(to_node_uid, FlowNodeDatum(new_to_node_flow_in, prev_to_node_flow_out))

            lark = Arc(from_node_uid, to_node_uid, FlowArcDatumWithUid(a.datum.capacity, new_flow, a.datum.uid))
            get['arcs'][from_node_uid][to_node_uid][a.datum.uid] = lark

            if(to_node_uid in get['residual_arcs'][from_node_uid]):
                get['residual_arcs'][from_node_uid].pop(to_node_uid)
            if(from_node_uid in get['residual_arcs'][to_node_uid]):
                get['residual_arcs'][to_node_uid].pop(from_node_uid)

            if(get['node_to_node_capacity'][from_node_uid][to_node_uid] > get['node_to_node_flow'][from_node_uid][to_node_uid]):
                residue = round(get['node_to_node_capacity'][from_node_uid][to_node_uid] - get['node_to_node_flow'][from_node_uid][to_node_uid], TOL)
                rarc1 = Arc(from_node_uid, to_node_uid, ResidualDatum(residue, 'push'))
                get['residual_arcs'][from_node_uid][to_node_uid] = rarc1
            if(get['node_to_node_flow'][from_node_uid][to_node_uid] > 0.0):
                residue = round(get['node_to_node_flow'][from_node_uid][to_node_uid],TOL)   
                rarc2 = Arc(to_node_uid, from_node_uid, ResidualDatum(residue, 'pull'))
                get['residual_arcs'][to_node_uid][from_node_uid] = rarc2
    return get

def pdg(G):
    if(debug):
        for n in G.setOfNodes:
            print('Node:',n.uid, n.datum.flowIn, n.datum.flowOut)
        for a in G.setOfArcs:
            print('Arc :',a.fromNode.uid, a.fromNode.datum.flowIn, a.fromNode.datum.flowOut, a.toNode.uid, a.toNode.datum.flowIn, a.toNode.datum.flowOut,a.datum)
 
if __name__ == '__main__':
    progz = ['neato','dot','twopi','circo','fdp','nop']
    #Seems that dot and neato work, the others don't look good, or break.
    #test_1()
    #test_2()
    #test_3()
    #example_1()
    #example_4()
    example_5()
    #example_2()
    #example_prop_e()
