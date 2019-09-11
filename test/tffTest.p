tff(s,type,s: $tType).
tff(t,type,t: $tType).
tff(p,type,p: (s * t) > $o ).
tff(graph,axiom,
    ! [X: s,Y: t,Z: s] : imply(p(X,Y) & p(X,Z),Y = Z) ).
