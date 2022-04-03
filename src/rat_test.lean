import data.hash_map
import data.nat.basic
import data.rat.basic

def point := ℚ × ℚ

instance : has_repr point :=
  ⟨λ p, "(" ++ (repr p.1) ++ ", " ++ (repr p.2) ++ ")"⟩

def rat_hash (a : ℚ) : ℕ :=
  (a.num * a.denom).nat_abs

def point_hash : point → ℕ
| (a, b) := rat_hash a + rat_hash b

#eval point_hash (-1/4, 5/11)

def test_list : list (Σ (_ : point), list point) :=
  [
    (sigma.mk (0, 1) [(1/2, 1/2)]),
    (sigma.mk (1, 2) [(3/2, 3/2)]),
    (sigma.mk (2, 3) [(1/2, 1/2)]),
    (sigma.mk (3, 4) [(1/2, 1/2)])
  ]
#eval test_list
#eval hash_map.of_list test_list point_hash

def grid_1D := hash_map ℚ (λ _, list ℚ)

-- TODO: write a mod method for rationals, since it's currently casting them to naturals or integers and giving us a degenerate mod implementation
instance : has_mod ℚ :=
  has_mod (a : ℚ) (b : ℚ) :=

#check has_mod ℚ
#eval 2 % 9/3
-- #eval 3/2 % 1/3

-- def rat_mod : ℚ → ℚ → ℚ

def grid_1D_points (ε : ℚ) : list ℚ → grid_1D
| [] := mk_hash_map rat_hash
| (x :: xs) :=
    let g := grid_1D_points xs in
    let bucket_idx :=
    let l := g.find

-- def grid_points : list (Σ (_ : point), list point)

-- def hash_map_test : hash_map (ℚ × ℚ) (λ _, list point) :=
--   let res := mk_hash_map {point} {λ _, list point} point_hash 31 in
--   res


-- def close_pairs : list
