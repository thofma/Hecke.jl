

function discriminant(O::NumFieldOrd, K::NumField)
  K = nf(O)
  if K == base_field(K)
    return discriminant(O)
  else
    return norm(discriminant(O), K)*discriminant(base_ring(O), K)^degree(O)
  end
end

discriminant(O::NumFieldOrd, ::FlintRationalField) = absolute_discriminant(O)


function norm(I::NumFieldOrdIdl, K::NumField)
  O = order(I)
  if K == base_field(O)
    return norm(I)
  else
    return norm(norm(I), K)
  end
end

function norm(I::NumFieldOrdIdl, ::FlintRationalField)
  return absolute_norm(I)
end


function absolute_degree(O::NumFieldOrd)
  return absolute_degree(nf(O))
end