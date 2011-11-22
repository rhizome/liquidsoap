# Catenate two lists.
# @category List
def list.append(x,y)
  x@y
end

# Alias for the <code>l[k]</code> notation.
# @category List
# @param a Key to look for
# @param l List of pairs (key,value)
def list.assoc(a,l)
  l[a]
end

# list.mem_assoc(key,l) returns true if l contains a pair
# (key,value)
# @category List
# @param a Key to look for
# @param l List of pairs (key,value)
def list.mem_assoc(a,l)
  v = list.assoc(a,l)
  # We check for existence, since "" may indicate
  # either a binding (a,"") or no binding..
  list.mem((a,v),l)
end

# Remove a pair from an associative list
# @category List
# @param a Key of pair to be removed
# @param l List of pairs (key,value)
def list.remove_assoc(a,l)
  if list.mem_assoc(a,l) then list.remove((a,list.assoc(a,l)),l) else l end
end
