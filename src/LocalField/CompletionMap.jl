
# Interface for implementing maps to a completion.

# S is the type of the order (the codomain) and T is the elem_type of the order
mutable struct NACompletionMap{DomType, CodomType} <: Map{DomType, CodomType, HeckeMap, NACompletionMap}
    
    header::MapHeader
    prec # precision parameter    

    # We often need to do two separate refinement computations for the forward/backward maps.
    # This is why we store two contexts. However, it is possible to leave these fields undefined.
    forward_map_sharpening_ctx
    backward_map_sharpening_ctx

    function NACompletionMap{DomType, CodomType}(K::DomType, Kp::CodomType, embedding_map,
                                               lift_map, f_sharpening_ctx, b_sharpening_ctx) where {DomType<:NumField, CodomType<:NALocalField}
        
    
        self = new{DomType, CodomType}()
        self.forward_map_sharpening_ctx = f_sharpening_ctx
        self.backward_map_sharpening_ctx = b_sharpening_ctx
        self.prec = nothing

        self.header = MapHeader(K, Kp, embedding_map, lift_map)
        return self
    end

    # Constructor that infers types. 
    function NACompletionMap(K, Kp, embedding_map, lift_map, forward_ctx, backward_ctx)
        return NACompletionMap{typeof(K), typeof(Kp)}(K, Kp, embedding_map, lift_map, forward_ctx, backward_ctx)
    end
end


function forward_sharpening_context(mp::Map(NACompletionMap))
    return mp.forward_map_sharpening_ctx
end

function backward_sharpening_context(mp::Map(NACompletionMap))
    return mp.backward_map_sharpening_ctx
end
