




DCStoreCreate := function()
  local dcStore;
  dcStore := rec( isCanonical := true, canonizingElmnt := fail, child := [], stabilizer := fail
                );
  return dcStore;
end;


DCStoreAddChild := function(dcStore,i)
  dcStore.child[i] := DCStoreCreate();
end;


DCStoreAddStabilizer := function(dcStore,stab)
  dcStore.stabilizer := stab;
end;


DCStoreAddCanonizingElmnt := function(dcStore,canElmnt)
  dcStore.isCanonical := false;
  dcStore.canonizingElmnt := canElmnt;
end;

