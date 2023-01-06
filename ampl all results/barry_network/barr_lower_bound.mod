# Global parameters
param adm_cost >= 0;
param bbdx_flow_cost >= 0;
param adm_usage_cost >= 0;
param arc_capacity >= 0;

# Cycles and number of rings per cycle
set CYCLES;
set NODES {c in CYCLES} circular := 
  (setof {i in 1 .. length(c)} substr(c, i, 1) );

param rings{CYCLES} integer >= 0;

set HUB_NODES := union {c in CYCLES} NODES[c];
param bbdx{HUB_NODES} binary;

set RING_NODES := union {c in CYCLES} 
  (union {n in NODES[c]} (setof {i in 1 .. rings[c]} c & "_" & n & "_" & i ) );


# Transportation demands
set COMMODITIES within (HUB_NODES cross HUB_NODES);
param demand{COMMODITIES} >= 0;

# All hubs that are adjacent - transportation cost
set EDGES := union {c in CYCLES} (
    setof {n in NODES[c]} (n, next(n, NODES[c])) union
    setof {n in NODES[c]} (n, prev(n, NODES[c])) );

param cost_symmetric_raw{EDGES} default 0;

# Ring to city arcs
set ARCS_0 := union {n in HUB_NODES} (union {c in CYCLES: n in NODES[c]} 
  (setof {i in 1 .. rings[c]} (c & "_" & n & "_" & i, n) ));

# City to ring arcs
set ARCS_1 := union {n in HUB_NODES} (union {c in CYCLES: n in NODES[c]} 
  (setof {i in 1 .. rings[c]} (n, c & "_" & n & "_" & i) ));

# NOTE that ARCS_0 and ARCS_1 can be conveniently used as sets
# defining links between ring and hub nodes. We will use this below.

# Ring arcs on the same cycle
set ARCS_2 := union {c in CYCLES} (union {i in 1 .. rings[c]} (
  (setof {n in NODES[c]} 
  (c & "_" & n & "_" & i, c & "_" & next(n, NODES[c]) & "_" & i) ) union
  (setof {n in NODES[c]} 
  (c & "_" & n & "_" & i, c & "_" & prev(n, NODES[c]) & "_" & i) )));

# Add for forward arcs only, for capacity constraint
set ARCS_2_forward := union {c in CYCLES} (union {i in 1 .. rings[c]} (
  (setof {n in NODES[c]} 
  (c & "_" & n & "_" & i, c & "_" & next(n, NODES[c]) & "_" & i) )));

# Ring to ring arcs at hubs (possibly crossing cycles); must have BBDX at hub
set ARCS_3 := union {n in HUB_NODES: bbdx[n] = 1}
  (union {(c, d) in CYCLES cross CYCLES: n in NODES[c] and n in NODES[d]} 
  (setof {i in 1 .. rings[c], j in 1 .. rings[d]: c <> d or i <> j}   
  (c & "_" & n & "_" & i, d & "_" & n & "_" & j) ));

# Defines costs for type 2 arcs. Note that this is dependent on only 1
# Direction of raw costs being loaded (the other is set to 0).
param flow_cost{(i,j) in ARCS_2} :=
  cost_symmetric_raw[substr(i, length(i)-2, 1), substr(j, length(j)-2, 1)]
  + cost_symmetric_raw[substr(j, length(j)-2, 1), substr(i, length(i)-2, 1)];

# Variables
var adm{RING_NODES} binary;
var flow0{ARCS_0, COMMODITIES} >= 0;
var flow1{ARCS_1, COMMODITIES} >= 0;
var flow2{ARCS_2, COMMODITIES} >= 0;
var flow3{ARCS_3, COMMODITIES} >= 0;

# Objective
minimize Total_Cost:
  adm_cost * (sum {i in RING_NODES} adm[i]) 
  + adm_usage_cost * (sum {(i,j) in ARCS_0, (k,l) in COMMODITIES} flow0[i,j,k,l]
  + sum {(i,j) in ARCS_1, (k,l) in COMMODITIES} flow1[i,j,k,l])
  + sum {(i,j) in ARCS_2, (k,l) in COMMODITIES} (flow_cost[i,j] * flow2[i,j,k,l])
  + (2 * adm_usage_cost + bbdx_flow_cost) 
  * (sum {(i,j) in ARCS_3, (k,l) in COMMODITIES} flow3[i,j,k,l]);

# Constraints given to you
subject to
  Capacity {(i,j) in ARCS_2_forward}: 
    sum {(k,l) in COMMODITIES} (flow2[i,j,k,l] + flow2[j,i,k,l]) <= arc_capacity;
    
  
  Flowtohub {(i,j) in ARCS_0, (k,l) in COMMODITIES: j <> l}:
    flow0[i,j,k,l] = 0;
  
  Flowfromhub {(i,j) in ARCS_1, (k,l) in COMMODITIES: i <> k}:
    flow1[i,j,k,l] = 0;
	  
  Admtohub {(i,j) in ARCS_0, (k,l) in COMMODITIES: j = l}:
    flow0[i,j,k,l] <= 2 * arc_capacity * adm[i];
  
  Admfromhub {(i,j) in ARCS_1, (k,l) in COMMODITIES: i = k}:
    flow1[i,j,k,l] <= 2 * arc_capacity * adm[j];
	  
  Admtype3orig {(i,j) in ARCS_3, (k,l) in COMMODITIES}:
    flow3[i,j,k,l] <= 2 * arc_capacity * adm[i];
	
  Admtype3final {(i,j) in ARCS_3, (k,l) in COMMODITIES}:
    flow3[i,j,k,l] <= 2 * arc_capacity * adm[j];
	
  Demandatdest {(k,l) in COMMODITIES}:
    sum {i in RING_NODES: (i,l) in ARCS_0} flow0[i,l,k,l] = demand[k,l];
	  
  Demandatorig {(k,l) in COMMODITIES}:
    sum {j in RING_NODES: (k,j) in ARCS_1} flow1[k,j,k,l] = demand[k,l];
	  
  Balance {j in RING_NODES, (k,l) in COMMODITIES}:
      sum {a in HUB_NODES:  (a,j) in ARCS_1} flow1[a,j,k,l] 
    + sum {b in RING_NODES: (b,j) in ARCS_2} flow2[b,j,k,l]
    + sum {c in RING_NODES: (c,j) in ARCS_3} flow3[c,j,k,l]
    = sum {d in HUB_NODES:  (j,d) in ARCS_0} flow0[j,d,k,l]
    + sum {e in RING_NODES: (j,e) in ARCS_2} flow2[j,e,k,l]
    + sum {f in RING_NODES: (j,f) in ARCS_3} flow3[j,f,k,l];
    # new constraint based on witthin cycle optimized and total demand
subject to ai1:
	adm["ABLNIKMQHD_A_1"]+adm["ABLNIKMQHD_A_2"]+adm["ABLNIKMQHD_A_3"]+adm["ABLNIKMQHD_A_4"]>=4;
subject to ai2:
	adm["ABLNIKMQHD_B_1"]+adm["ABLNIKMQHD_B_2"]+adm["ABLNIKMQHD_B_3"]+adm["ABLNIKMQHD_B_4"]>=1;
subject to ai3:
	adm["ABLNIKMQHD_L_1"]+adm["ABLNIKMQHD_L_2"]+adm["ABLNIKMQHD_L_3"]+adm["ABLNIKMQHD_L_4"]>=1;
subject to ai4:
	adm["ABLNIKMQHD_N_1"]+adm["ABLNIKMQHD_N_2"]+adm["ABLNIKMQHD_N_3"]+adm["ABLNIKMQHD_N_4"]>=1;
subject to ai5:
	adm["ABLNIKMQHD_I_1"]+adm["ABLNIKMQHD_I_2"]+adm["ABLNIKMQHD_I_3"]+adm["ABLNIKMQHD_I_4"]+adm["IPTUJFK_I_1"]+adm["IPTUJFK_I_2"]+adm["IPTUJFK_I_3"]>=3;
subject to ai6:
	adm["ABLNIKMQHD_K_1"]+adm["ABLNIKMQHD_K_2"]+adm["ABLNIKMQHD_K_3"]+adm["ABLNIKMQHD_K_4"]+adm["IPTUJFK_K_1"]+adm["IPTUJFK_K_2"]+adm["IPTUJFK_K_3"]>=1;
subject to ai7:
	adm["ABLNIKMQHD_M_1"]+adm["ABLNIKMQHD_M_2"]+adm["ABLNIKMQHD_M_3"]+adm["ABLNIKMQHD_M_4"]+adm["MEGRCOSQ_M_1"]+adm["MEGRCOSQ_M_2"]+adm["MEGRCOSQ_M_3"]+adm["MEGRCOSQ_M_4"]+adm["MEGRCOSQ_M_5"]+adm["MEGRCOSQ_M_6"]>=1;
subject to ai8:
	adm["ABLNIKMQHD_Q_1"]+adm["ABLNIKMQHD_Q_2"]+adm["ABLNIKMQHD_Q_3"]+adm["ABLNIKMQHD_Q_4"]+adm["MEGRCOSQ_Q_1"]+adm["MEGRCOSQ_Q_2"]+adm["MEGRCOSQ_Q_3"]+adm["MEGRCOSQ_Q_4"]+adm["MEGRCOSQ_Q_5"]+adm["MEGRCOSQ_Q_6"]>=1;
subject to ai9:
	adm["ABLNIKMQHD_H_1"]+adm["ABLNIKMQHD_H_2"]+adm["ABLNIKMQHD_H_3"]+adm["ABLNIKMQHD_H_4"]>=1;
subject to ai10:
	adm["ABLNIKMQHD_D_1"]+adm["ABLNIKMQHD_D_2"]+adm["ABLNIKMQHD_D_3"]+adm["ABLNIKMQHD_D_4"]>=1;
subject to ai11:
	adm["MEGRCOSQ_E_1"]+adm["MEGRCOSQ_E_2"]+adm["MEGRCOSQ_E_3"]+adm["MEGRCOSQ_E_4"]+adm["MEGRCOSQ_E_5"]+adm["MEGRCOSQ_E_6"]>=1;
subject to ai12:
	adm["MEGRCOSQ_G_1"]+adm["MEGRCOSQ_G_2"]+adm["MEGRCOSQ_G_3"]+adm["MEGRCOSQ_G_4"]+adm["MEGRCOSQ_G_5"]+adm["MEGRCOSQ_G_6"]>=5;
subject to ai13:
	adm["MEGRCOSQ_R_1"]+adm["MEGRCOSQ_R_2"]+adm["MEGRCOSQ_R_3"]+adm["MEGRCOSQ_R_4"]+adm["MEGRCOSQ_R_5"]+adm["MEGRCOSQ_R_6"]>=3;
subject to ai14:
	adm["MEGRCOSQ_C_1"]+adm["MEGRCOSQ_C_2"]+adm["MEGRCOSQ_C_3"]+adm["MEGRCOSQ_C_4"]+adm["MEGRCOSQ_C_5"]+adm["MEGRCOSQ_C_6"]>=1;
subject to ai15:
	adm["MEGRCOSQ_O_1"]+adm["MEGRCOSQ_O_2"]+adm["MEGRCOSQ_O_3"]+adm["MEGRCOSQ_O_4"]+adm["MEGRCOSQ_O_5"]+adm["MEGRCOSQ_O_6"]>=5;
subject to ai16:
	adm["MEGRCOSQ_S_1"]+adm["MEGRCOSQ_S_2"]+adm["MEGRCOSQ_S_3"]+adm["MEGRCOSQ_S_4"]+adm["MEGRCOSQ_S_5"]+adm["MEGRCOSQ_S_6"]>=2;
subject to ai17:
	adm["IPTUJFK_P_1"]+adm["IPTUJFK_P_2"]+adm["IPTUJFK_P_3"]>=2;
subject to ai18:
	adm["IPTUJFK_T_1"]+adm["IPTUJFK_T_2"]+adm["IPTUJFK_T_3"]>=1;
subject to ai19:
	adm["IPTUJFK_U_1"]+adm["IPTUJFK_U_2"]+adm["IPTUJFK_U_3"]>=1;
subject to ai20:
	adm["IPTUJFK_J_1"]+adm["IPTUJFK_J_2"]+adm["IPTUJFK_J_3"]>=3;
subject to ai21:
	adm["IPTUJFK_F_1"]+adm["IPTUJFK_F_2"]+adm["IPTUJFK_F_3"]>=2;
 
# Cuts you make
# subject to
	# TODO
