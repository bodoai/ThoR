import ThoR

alloy dotjoin_sig_rel
  sig a {
    r : a
  }
  fact {
    some (a.r)
  }
end

create dotjoin_sig_rel

-- some (a . r)
#check dotjoin_sig_rel.facts.f0

alloy dotjoin_rel_rel
  sig a {
    r : a
  }
  fact {
    some (r.r)
  }
end

#create dotjoin_rel_rel

-- some (r . r) / some (dotjoin_rel_rel.vars.r . dotjoin_rel_rel.vars.r)
#check dotjoin_rel_rel.facts.f0

alloy union_rel_rel
  sig a {
    r : a
  }
  fact {
    some (r+r)
  }
end
#create union_rel_rel

#check union_rel_rel.facts.f0
