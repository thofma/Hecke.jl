################################################################################
#
#  AVL Trees
#
################################################################################
#
# AVL Trees
#
# Original implementation under MIT License from
# https://github.com/JuliaCollections/DataStructures.jl/blob/2a73458c86186b34a19247e572b4fbb526b07a2b/src/avl_tree.jl#L256-L260
#
# Copyright (c) 2013 Dahua Lin
#
# Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

# Restrictions:
# Keys are unique

# Type for nodes
mutable struct AVLTreeNode{K}
  height::Int8                               # height of subtree
  left_child::Union{AVLTreeNode{K}, Nothing}  # things < node
  right_child::Union{AVLTreeNode{K}, Nothing} # things > node
  subsize::Int32                             # cardinality of subtree
  data::K

  AVLTreeNode{K}(d::K) where K = new{K}(1, nothing, nothing, 1, d)
end

#"""
#    AVLTree{T}
#
#Construct new `AVLTree` with keys of type `T`.
#
## Example
#
#```jldoctest
#julia> tree = AVLTree{Int64}()
#AVLTree{Int64}(nothing, 0)
#```
#"""
mutable struct AVLTree{T, F, Feq}
  root::Union{AVLTreeNode{T}, Nothing}
  count::Int                             # length
  cmp::F                                 # binary comparison function (<)
  eq::Feq                                # binary equality function (==)

  # Default comparison is < and default equality
  function AVLTree{T}() where T 
    return new{T, typeof(<), typeof(==)}(nothing, 0, <, ==)
  end

  function AVLTree{T, F, Feq}(cmp::F, eq::Feq) where {T, F, Feq}
    return new{T, F, Feq}(nothing, 0, cmp, eq)
  end
end

AVLTree{T}(cmp::F, eq::Feq) where {T, F, Feq} =  AVLTree{T, F, Feq}(cmp, eq)

"""
    length(tree::AVLTree)

Return number of elements in AVL tree `tree`.
"""
Base.length(tree::AVLTree) = tree.count

get_height(node::Union{AVLTreeNode, Nothing}) = (node == nothing) ? Int8(0) : node.height

# balance is the difference of height between left_child and right_child of a node.
function get_balance(node::Union{AVLTreeNode, Nothing})
  if node == nothing
    return 0
  else
    return get_height(node.left_child) - get_height(node.right_child)
  end
end

# computes the height of the subtree, which basically is
# one added the maximum of the height of the left subtree and right subtree
compute_height(node::AVLTreeNode) = Int8(1) + max(get_height(node.left_child), get_height(node.right_child))

get_subsize(node::Union{AVLTreeNode, Nothing}) = (node == nothing) ? Int32(0) : node.subsize

# compute the subtree size
function compute_subtree_size(node::Union{AVLTreeNode, Nothing})
  if node == nothing
    return Int32(0)
  else
    L = get_subsize(node.left_child)
    R = get_subsize(node.right_child)
    return (L + R + Int32(1))
  end
end

"""
    left_rotate(node_x::AVLTreeNode)

Performs a left-rotation on `node_x`, updates height of the nodes, and returns the rotated node.
"""
function left_rotate(z::AVLTreeNode)
  y = z.right_child
  α = y.left_child
  y.left_child = z
  z.right_child = α
  z.height = compute_height(z)
  y.height = compute_height(y)
  z.subsize = compute_subtree_size(z)
  y.subsize = compute_subtree_size(y)
  return y
end

"""
    right_rotate(node_x::AVLTreeNode)

Performs a right-rotation on `node_x`, updates height of the nodes, and returns the rotated node.
"""
function right_rotate(z::AVLTreeNode)
  y = z.left_child
  α = y.right_child
  y.right_child = z
  z.left_child = α
  z.height = compute_height(z)
  y.height = compute_height(y)
  z.subsize = compute_subtree_size(z)
  y.subsize = compute_subtree_size(y)
  return y
end

#"""
#    minimum_node(tree::AVLTree, node::AVLTreeNode)
#
#Returns the AVLTreeNode with minimum value in subtree of `node`.
#"""
function minimum_node(node::Union{AVLTreeNode, Nothing})
  while node !== nothing && node.left_child !== nothing
    node = node.left_child
  end
  return node
end

function search_node(tree::AVLTree{K}, d::K) where K
  prev = nothing
  node = tree.root
  while node != nothing && node.data != nothing && !tree.eq(node.data, d)

    prev = node
    if tree.cmp(d, node.data)
      node = node.left_child
    else
      node = node.right_child
    end
  end

  return (node == nothing) ? prev : node
end

function Base.haskey(tree::AVLTree{K}, k::K) where K
  (tree.root == nothing) && return false
  node = search_node(tree, k)
  return tree.eq(node.data, k)
end

Base.in(key, tree::AVLTree) = haskey(tree, key)

function insert_node(tree::AVLTree, node::Nothing, key::K) where K
  return AVLTreeNode{K}(key)
end

function insert_node(tree::AVLTree{K}, node::AVLTreeNode{K}, key::K) where K
  if tree.cmp(key, node.data)
    node.left_child = insert_node(tree, node.left_child, key)
  else
    node.right_child = insert_node(tree, node.right_child, key)
  end

  node.subsize = compute_subtree_size(node)
  node.height = compute_height(node)
  balance = get_balance(node)

  if balance > 1
    if tree.cmp(key, node.left_child.data)
      return right_rotate(node)
    else
      node.left_child = left_rotate(node.left_child)
      return right_rotate(node)
    end
  end

  if balance < -1
    if tree.cmp(node.right_child.data, key)
      return left_rotate(node)
    else
      node.right_child = right_rotate(node.right_child)
      return left_rotate(node)
    end
  end

  return node
end

function Base.insert!(tree::AVLTree{K}, d::K) where K
  haskey(tree, d) && return tree

  tree.root = insert_node(tree, tree.root, d)
  tree.count += 1
  return tree
end

function Base.push!(tree::AVLTree{K}, key::K) where K
  insert!(tree, key)
end

function delete_node!(tree::AVLTree{K}, node::AVLTreeNode{K}, key::K) where K
  if tree.cmp(key, node.data)
    node.left_child = delete_node!(tree, node.left_child, key)
  elseif tree.cmp(node.data, key)
    node.right_child = delete_node!(tree, node.right_child, key)
  else
    if node.left_child == nothing
      result = node.right_child
      return result
    elseif node.right_child == nothing
      result = node.left_child
      return result
    else
      result = minimum_node(node.right_child)
      node.data = result.data
      node.right_child = delete_node!(tree, node.right_child, result.data)
    end
  end

  node.subsize = compute_subtree_size(node)
  node.height = compute_height(node)
  balance = get_balance(node)

  if balance > 1
    if get_balance(node.left_child) >= 0
      return right_rotate(node)
    else
      node.left_child = left_rotate(node.left_child)
      return right_rotate(node)
    end
  end

  if balance < -1
    if get_balance(node.right_child) <= 0
      return left_rotate(node)
    else
      node.right_child = right_rotate(node.right_child)
      return left_rotate(node)
    end
  end

  return node
end

function Base.delete!(tree::AVLTree{K}, k::K) where K
  # if the key is not in the tree, do nothing and return the tree
  !haskey(tree, k) && return tree

  # if the key is present, delete it from the tree
  tree.root = delete_node!(tree, tree.root, k)
  tree.count -= 1
  return tree
end

# """
#     sorted_rank(tree::AVLTree{K}, key::K) where K
# 
# Returns the rank of `key` present in the `tree`, if it present. A `KeyError` is thrown if `key`
# is not present.
# 
# # Examples
# 
# ```jldoctest
# julia> tree = AVLTree{Int}();
# 
# julia> for k in 1:2:20
#            push!(tree, k)
#        end
# 
# julia> sorted_rank(tree, 17)
# 9
# ```
# """
function sorted_rank(tree::AVLTree{K}, key::K) where K
  !haskey(tree, key) && throw(KeyError(key))
  node = tree.root
  rank = 0
  while !tree.eq(node.data, key)
    if tree.cmp(node.data, key)
      rank += (1 + get_subsize(node.left_child))
      node = node.right_child
    else
      node = node.left_child
    end
  end
  rank += (1 + get_subsize(node.left_child))
  return rank
end

# """
#     getindex(tree::AVLTree{K}, i::Integer) where K
# 
# Considering the elements of `tree` sorted, returns the `i`-th element in `tree`. Search
# operation is performed in \$O(\\log n)\$ time complexity.
# 
# # Examples
# 
# ```jldoctest
# julia> tree = AVLTree{Int}()
# AVLTree{Int64}(nothing, 0)
# 
# julia> for k in 1:2:20
#            push!(tree, k)
#        end
# 
# julia> tree[4]
# 7
# 
# julia> tree[8]
# 15
# ```
# """
#
# disable this footgun
function _getindex(tree::AVLTree{K}, ind::Integer) where K
  @boundscheck (1 <= ind <= tree.count) || throw(BoundsError("$ind should be in between 1 and $(tree.count)"))
  function traverse_tree(node::Union{AVLTreeNode, Nothing}, idx)
    if (node != nothing)
      L = get_subsize(node.left_child)
      if idx <= L
        return traverse_tree(node.left_child, idx)
      elseif idx == L + 1
        return node.data
      else
        return traverse_tree(node.right_child, idx - L - 1)
      end
    end
  end
  value = traverse_tree(tree.root, ind)
  return value
end

################################################################################
#
# Iteration
#
################################################################################

function _push_stack!(stack, node)
  while node !== nothing
    push!(stack, node)
    node = node.left_child
  end
  return stack
end

function _pop_and_push!(stack)
  node = pop!(stack)
  _push_stack!(stack, node.right_child)
  return node
end

function Base.iterate(tree::AVLTree{T}) where {T}
  node = tree.root
  if node === nothing
    return nothing
  end
  stack = AVLTreeNode{T}[]
  _push_stack!(stack, node)
  node = _pop_and_push!(stack)
  return node.data, stack
end

function Base.iterate(tree::AVLTree, stack)
  if length(stack) == 0
    return nothing
  end
  node = _pop_and_push!(stack)
  return node.data, stack
end
