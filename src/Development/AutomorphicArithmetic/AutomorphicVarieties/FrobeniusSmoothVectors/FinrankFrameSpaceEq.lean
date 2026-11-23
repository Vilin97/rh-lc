module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Mathlib.LinearAlgebra.Dimension.Basic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrYMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrameExtensionOfLocallyConstant
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FinrankStructMapYRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemPowSmulLe
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FramePointFiberNonempty
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FramePointYCoordEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.Topology.Sheaves.Presheaf

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgebraMapRangeSpanEqTopOfFiniteGenerators

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.algebraMap_range_span_eq_top_of_finite_generators :
    ∀ {k G M : Type} [Field k] [AddCommGroup M] [Module k M] (Y : Submodule k (G → k)) (C : ℕ) (a : G → M), Module.rank k Y ≤ C → (∀ f : M →ₗ[k] k, (fun g => f (a g)) ∈ Y) → ∃ T : Finset M, T.card ≤ C ∧ ∀ g, a g ∈ Submodule.span k (T : Set M) := by
  intro k G M _ _ _ Y C a hY ha
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent k (Set.range a)
  have hli' : LinearIndepOn k id b := hli
  let B := Module.Basis.extend hli'
  have hmem : ∀ x : b, (x : M) ∈ hli'.extend (Set.subset_univ b) :=
    fun x => hli'.subset_extend (Set.subset_univ b) x.2
  have hB : ∀ x : b, B ⟨x, hmem x⟩ = x := fun x => by
    simp only [B, Module.Basis.coe_extend]
  have hco : ∀ x y : b, B.coord ⟨x, hmem x⟩ (y : M) = if y = x then 1 else 0 := by
    intro x y
    rw [← hB y, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : y = x
    · subst h
      simp
    · have h' : (⟨(y : M), hmem y⟩ : hli'.extend (Set.subset_univ b)) ≠ ⟨x, hmem x⟩ := by
        intro e
        apply h
        apply Subtype.ext
        exact Subtype.mk.inj e
      simp [h, h']
  choose gx hgx using fun x : b => hbs x.2
  let φ : b → Y := fun x => ⟨fun g => B.coord ⟨x, hmem x⟩ (a g), ha (B.coord ⟨x, hmem x⟩)⟩
  have hφ : LinearIndependent k φ := by
    rw [linearIndependent_iff']
    intro s c hsum i hi
    have h1 := congrArg (fun y : Y => (y : G → k) (gx i)) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      ZeroMemClass.coe_zero, Pi.zero_apply, φ, hgx] at h1
    simpa [hco, hi] using h1
  have hcard : Cardinal.mk b ≤ C := hφ.cardinal_le_rank.trans hY
  have hfin : b.Finite := Cardinal.lt_aleph0_iff_set_finite.mp (hcard.trans_lt (Cardinal.natCast_lt_aleph0 (n := C)))
  haveI := hfin.fintype
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rw [Set.Finite.card_toFinset]
    rw [Cardinal.mk_fintype] at hcard
    exact_mod_cast hcard
  · intro g
    rw [Set.Finite.coe_toFinset, hspan]
    exact Submodule.subset_span ⟨g, rfl⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FinrankStructMapSRange

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.finrank_structMapS_range :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → Module.rank k (F.strS k) ≤ C₀ := by
  intro l _ k _ _ F C₀ hF
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k l] at h'
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).mp h')
  set χ := F.Ψ⁻¹ ^ 2 * F.delK k with hχ
  have hc : ((χ F.c : kˣ) : k) = -1 := by
    simp [hχ, Frame.delK, hF.del_c, hF.Ψ_c]
  let Z := Z1C F.loc (chRep χ) fun _ => (⊥ : Submodule k k)
  let f : Z →ₗ[k] (F.G0 → k) :=
    { toFun := fun x g => (x.1.1 g + ((χ g : k) * x.1.1 F.c - x.1.1 F.c) * 2⁻¹) * (F.Ψ g : k)
      map_add' := by
        intro x y
        funext g
        simp
        ring
      map_smul' := by
        intro r x
        funext g
        simp
        ring }
  have hker : Submodule.comap Z.subtype (continuousCoboundaries1 (chRep χ) fun _ => (⊥ : Submodule k k)) ≤ LinearMap.ker f := by
    rintro ⟨x, hx⟩ hb
    rw [Submodule.mem_comap] at hb
    obtain ⟨X, hX, -⟩ := hb
    rw [LinearMap.mem_ker]
    funext g
    have e1 := hX (g : F.Γ)
    have e2 := hX F.c
    simp only [Submodule.subtype_apply, chRep_apply, hc] at e1 e2
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    rw [e1, e2]
    field_simp
    ring
  let L := Submodule.liftQ _ f hker
  have hle : F.strS k ≤ LinearMap.range L := by
    intro a ha
    obtain ⟨x, hx, hx0, hax⟩ := frame_extension_of_locallyConstant hF a ha
    refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
    rw [Submodule.liftQ_apply]
    funext g
    simp [f, hx0, hax]
  calc Module.rank k (F.strS k) ≤ Module.rank k (LinearMap.range L) := Submodule.rank_mono hle
    _ ≤ Module.rank k (H1C F.loc (chRep χ) fun _ => (⊥ : Submodule k k)) := rank_range_le L
    _ ≤ C₀ := hF.b1p
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrameFiberEq

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.frame_fiber_eq :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (S : Space O F n) (I : Ideal S.A), S.x0 ≤ I → ∃ f : ResidueField O →+* S.A ⧸ I, (S.u.map (Ideal.Quotient.mk I)).IsBar f ∧ (∀ i j, IsLocallyConstant fun g => (S.u.map (Ideal.Quotient.mk I)).r g i j) ∧ Subring.closure (Set.range f ∪ {x | ∃ g i j, x = (S.u.map (Ideal.Quotient.mk I)).r g i j}) = ⊤ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S I hI
  have hB : ∀ b : S.B, (b : S.R) ∈ maximalIdeal S.R → S.inc b ∈ I := fun b hb =>
    hI (Ideal.mem_map_of_mem _ (show b ∈ S.mB from hb))
  have hm : ∀ a ∈ maximalIdeal O, algebraMap O S.A a ∈ I := fun a ha =>
    hB (algebraMap O S.B a) (map_nonunit (algebraMap O S.R) a ha)
  let f : ResidueField O →+* S.A ⧸ I :=
    Ideal.Quotient.lift (maximalIdeal O) ((Ideal.Quotient.mk I).comp (algebraMap O S.A))
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hm a ha)
  have hf : ∀ a : O, f (residue O a) = Ideal.Quotient.mk I (algebraMap O S.A a) := fun a => rfl
  have key : ∀ b : S.B, Ideal.Quotient.mk I (S.inc b) = f (res O S.R b) := fun b => by
    obtain ⟨a, ha⟩ := residue_surjective (res O S.R b)
    rw [← ha, hf, Ideal.Quotient.eq]
    have h1 : ((b - algebraMap O S.B a : S.B) : S.R) ∈ maximalIdeal S.R := by
      rw [← res_eq_zero_iff O]
      show res O S.R ((b : S.R) - algebraMap O S.R a) = 0
      rw [map_sub, AlgHom.commutes, ← ha]
      exact sub_self _
    have h2 := hB _ h1
    rwa [map_sub, AlgHom.commutes] at h2
  refine ⟨f, ⟨fun g i => ?_, fun v i g => ?_⟩, fun i j => ?_, ?_⟩
  · exact (key (S.aB g i)).trans (congrArg f (S.lift.2.1.1 g i))
  · exact (key (S.ψB v i g)).trans (congrArg f (S.lift.2.1.2 v i g))
  · have hle : S.x0 ^ 1 ≤ I := by rwa [pow_one]
    exact ((cont_u hF hn S).1.1 i j 1).comp (Ideal.Quotient.factor hle)
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | ⟨g, i, j, rfl⟩
      · exact Subring.subset_closure (Or.inl ⟨_, (key ⟨x, hx⟩).symm⟩)
      · exact Subring.subset_closure (Or.inr ⟨g, i, j, rfl⟩)
    | algebraMap a => exact Subring.subset_closure (Or.inl ⟨_, hf a⟩)
    | add x y hx hy h1 h2 => exact add_mem h1 h2
    | mul x y hx hy h1 h2 => exact mul_mem h1 h2
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FramePointAlgCoordEq

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.framePoint_alg_coord_eq :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F 3 Q), ρ.IsBar (algebraMap k Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → ∀ U : Subalgebra k Q, (∀ g, ρ.r g 1 0 ∈ U) → (fun g => (Subalgebra.toSubmodule U).mkQ (ρ.r g 2 0)) ∈ F.strS (Q ⧸ Subalgebra.toSubmodule U) := by
  intro l _ k _ _ F C₀ hF Q _ _ ρ hb ht hlc U hU
  have hz : ∀ g (i j : Fin 3), i < j → ρ.r g i j = 0 := by
    intro g i j hij
    have hm : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    rw [ht] at hm
    exact (Ideal.mem_bot).1 hm
  have hd : ∀ g (i : Fin 3), ρ.r g i i = algebraMap k Q ↑(F.Ψ ↑g ^ w 3 i) := hb.1
  have h21 : ∀ g, ρ.r g 2 1 ∈ U := by
    intro g
    have e : ρ.r g 2 1 = ρ.r (F.star g) 1 0 := by
      rw [(star hF).2.2.2.2 ρ g 1 0]
      rfl
    rw [e]
    exact hU _
  have w0 : w 3 0 = 1 := by simp [w]
  have w1 : w 3 1 = 0 := by simp [w]
  have w2 : w 3 2 = -1 := by simp [w]
  have hq : ∀ x : Q, x ∈ U → (Subalgebra.toSubmodule U).mkQ x = 0 := by
    intro x hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  refine ⟨(hlc 2 0).comp _, ?_, ?_, ?_⟩
  · intro g h
    dsimp only
    rw [map_mul, Matrix.mul_apply, Fin.sum_univ_three, hd h 0, hd g 2, w0, w2, zpow_one, _root_.zpow_neg_one]
    have e1 : ρ.r g 2 0 * algebraMap k Q ↑(F.Ψ ↑h) = (↑(F.Ψ ↑h) : k) • ρ.r g 2 0 := by
      rw [Algebra.smul_def, mul_comm]
    have e3 : algebraMap k Q ↑(F.Ψ ↑g)⁻¹ * ρ.r h 2 0 = (↑(F.Ψ ↑g)⁻¹ : k) • ρ.r h 2 0 := by
      rw [Algebra.smul_def]
    rw [e1, e3, map_add (f := _), map_add (f := _), map_smul, map_smul, hq _ (U.mul_mem (h21 g) (hU h)), add_zero]
  · intro g
    dsimp only
    rw [(star hF).2.2.2.2 ρ g 2 0]
    rfl
  · intro v
    obtain ⟨t, ht2⟩ := hF.f3 v
    refine ⟨((↑(F.Ψ (F.loc v t)) : k) - ↑(F.Ψ (F.loc v t))⁻¹)⁻¹ • (Subalgebra.toSubmodule U).mkQ (ρ.r (F.loc0 v t) 2 0), fun s => ?_⟩
    have hl : ∀ x, ((F.loc0 v x : F.G0) : F.Γ) = F.loc v x := fun _ => rfl
    have e := congrArg (fun M => M 2 0) (ρ.ord v ![t, t, s])
    have z01 := hz (F.loc0 v t) 0 1 (by decide)
    have z02 := hz (F.loc0 v t) 0 2 (by decide)
    have z12 := hz (F.loc0 v t) 1 2 (by decide)
    have y01 := hz (F.loc0 v s) 0 1 (by decide)
    have y02 := hz (F.loc0 v s) 0 2 (by decide)
    have y12 := hz (F.loc0 v s) 1 2 (by decide)
    simp (config := {decide := true}) only [ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, Matrix.mul_apply, Fin.sum_univ_three, Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.one_apply, Matrix.zero_apply, smul_eq_mul, z01, z02, z12, y01, y02, y12, hd, hb.2, hl, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg_one, Units.val_one, map_one, if_true, if_false, mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add] at e
    set x : k := ↑(F.Ψ (F.loc v t)) with hx
    set xi : k := ↑(F.Ψ (F.loc v t))⁻¹ with hxi
    set y : k := ↑(F.Ψ (F.loc v s)) with hy
    set yi : k := ↑(F.Ψ (F.loc v s))⁻¹ with hyi
    have key : algebraMap k Q ((xi - x) * (xi - 1)) * ρ.r (F.loc0 v s) 2 0 + algebraMap k Q ((xi - 1) * (y - yi)) * ρ.r (F.loc0 v t) 2 0 = -(ρ.r (F.loc0 v t) 2 1 * ρ.r (F.loc0 v t) 1 0 * (algebraMap k Q y - algebraMap k Q yi) + (algebraMap k Q xi - algebraMap k Q x) * ρ.r (F.loc0 v t) 2 1 * ρ.r (F.loc0 v s) 1 0) := by
      simp only [map_mul, map_sub, map_one]
      linear_combination e
    have hne1 : xi - 1 ≠ 0 := by
      intro h
      apply ht2
      have h' : (F.Ψ (F.loc v t))⁻¹ = 1 := Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h)
      rw [inv_eq_one.1 h', one_pow]
    have hne2 : xi - x ≠ 0 := by
      intro h
      apply ht2
      have h' : (F.Ψ (F.loc v t))⁻¹ = F.Ψ (F.loc v t) := Units.ext (sub_eq_zero.1 h)
      calc F.Ψ (F.loc v t) ^ 2 = (F.Ψ (F.loc v t))⁻¹ * F.Ψ (F.loc v t) := by rw [sq, h']
        _ = 1 := inv_mul_cancel _
    have hne3 : x - xi ≠ 0 := fun h => hne2 (by rw [← neg_sub, h, neg_zero])
    have hc : (xi - x) * (xi - 1) ≠ 0 := mul_ne_zero hne2 hne1
    dsimp only
    rw [smul_smul, ← map_smul, ← sub_eq_zero, ← map_sub]
    apply hq
    have eq : ρ.r (F.loc0 v s) 2 0 - ((y - yi) * (x - xi)⁻¹) • ρ.r (F.loc0 v t) 2 0 = algebraMap k Q ((xi - x) * (xi - 1))⁻¹ * (algebraMap k Q ((xi - x) * (xi - 1)) * ρ.r (F.loc0 v s) 2 0 + algebraMap k Q ((xi - 1) * (y - yi)) * ρ.r (F.loc0 v t) 2 0) := by
      rw [Algebra.smul_def, mul_add, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
      have h3 : ((xi - x) * (xi - 1))⁻¹ * ((xi - 1) * (y - yi)) = -((y - yi) * (x - xi)⁻¹) := by
        field_simp
        ring
      rw [h3, map_neg, neg_mul, sub_eq_add_neg]
    rw [eq, key]
    exact mul_mem (U.algebraMap_mem _) (neg_mem (add_mem (mul_mem (mul_mem (h21 _) (hU _)) (sub_mem (U.algebraMap_mem _) (U.algebraMap_mem _))) (mul_mem (mul_mem (sub_mem (U.algebraMap_mem _) (U.algebraMap_mem _)) (h21 _)) (hU _))))
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FinrankFrameSpaceEq

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem dim_gen (k Q : Type) [Field k] [CommRing Q] [Algebra k Q] (T : Finset Q) (m : ℕ) (h : T.card ≤ m)
    (ht : Algebra.adjoin k (T : Set Q) = ⊤) : ringKrullDim Q ≤ (m : ℕ) := by
  have hs : Function.Surjective (MvPolynomial.aeval (R := k) (fun t : T => (t : Q))) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    simpa using ht
  refine (ringKrullDim_le_of_surjective (MvPolynomial.aeval (R := k) (fun t : T => (t : Q))).toRingHom hs).trans ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_coe]
  exact_mod_cast h

private theorem point {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}
    (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F n Q)
    (hb : ρ.IsBar (algebraMap k Q)) (ht : ρ.triM = ⊥) (hc : ∀ i j, IsLocallyConstant fun g => ρ.r g i j) :
    ∃ T : Finset Q, T.card ≤ 2 * C₀ ∧ ∀ g i j, ρ.r g i j ∈ Algebra.adjoin k (T : Set Q) := by
  classical
  have up : ∀ g i j, i < j → ρ.r g i j = 0 := fun g i j h => by
    have : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, h, rfl⟩
    rwa [ht, Ideal.mem_bot] at this
  have red : ∀ U : Subalgebra k Q, (∀ g i j, j < i → ρ.r g i j ∈ U) → ∀ g i j, ρ.r g i j ∈ U := fun U h g i j => by
    rcases lt_trichotomy i j with h1 | rfl | h1
    · rw [up g i j h1]; exact zero_mem _
    · rw [hb.1]; exact U.algebraMap_mem _
    · exact h g i j h1
  rcases hn with rfl | rfl
  · obtain ⟨T, h1, h2⟩ := algebraMap_range_span_eq_top_of_finite_generators (F.strS k) C₀ _ (finrank_structMapS_range hF)
      fun f => Frame.strS_map f (framePoint_fiber_nonempty hF Q ρ hb ht hc)
    refine ⟨T, by omega, red _ fun g i j h => ?_⟩
    obtain ⟨rfl, rfl⟩ : i = 1 ∧ j = 0 := by omega
    exact Algebra.span_le_adjoin k _ (h2 g)
  · obtain ⟨T, h1, h2⟩ := algebraMap_range_span_eq_top_of_finite_generators (F.strY k) C₀ _ (finrank_structMapY_range hF)
      fun f => Frame.strY_map f (framePoint_y_coord_eq hF Q ρ hb ht hc)
    have hy : ∀ g, ρ.r g 1 0 ∈ Algebra.adjoin k (T : Set Q) := fun g => Algebra.span_le_adjoin k _ (h2 g)
    obtain ⟨T', h3, h4⟩ := algebraMap_range_span_eq_top_of_finite_generators (F.strS k) C₀ _ (finrank_structMapS_range hF)
      fun f => Frame.strS_map f (framePoint_alg_coord_eq hF Q ρ hb ht hc _ hy)
    obtain ⟨σ, hσ⟩ := (Subalgebra.toSubmodule (Algebra.adjoin k (T : Set Q))).mkQ_surjective.hasRightInverse
    have hle : Algebra.adjoin k (T : Set Q) ≤ Algebra.adjoin k ((T ∪ T'.image σ : Finset Q) : Set Q) :=
      Algebra.adjoin_mono (by simp)
    refine ⟨T ∪ T'.image σ, (Finset.card_union_le _ _).trans ?_, red _ fun g i j h => ?_⟩
    · have := Finset.card_image_le (s := T') (f := σ)
      omega
    have hij : (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 2 ∧ j = 0) := by omega
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hle (hy g)
    · have h5 : ρ.r (F.star g) 1 0 = ρ.r g 2 1 := (UpperTheory.V.Fr.star hF).2.2.2.2 ρ g 1 0
      rw [← h5]
      exact hle (hy _)
    · have h5 : Submodule.span k (T' : Set _) ≤ (Subalgebra.toSubmodule (Algebra.adjoin k
          ((T ∪ T'.image σ : Finset Q) : Set Q))).map (Subalgebra.toSubmodule (Algebra.adjoin k (T : Set Q))).mkQ :=
        Submodule.span_le.2 fun t ht' => ⟨σ t, Algebra.subset_adjoin (by
          simp only [Finset.coe_union, Finset.coe_image]
          exact Or.inr ⟨t, ht', rfl⟩), hσ t⟩
      obtain ⟨x, hx, hx'⟩ := h5 (h4 g)
      have h6 : x - ρ.r g 2 0 ∈ Algebra.adjoin k (T : Set Q) := (Submodule.Quotient.eq _).1 hx'
      have h7 := sub_mem (show x ∈ Algebra.adjoin k ((T ∪ T'.image σ : Finset Q) : Set Q) from hx) (hle h6)
      rwa [sub_sub_cancel] at h7

theorem UpperTheory.V.Fr.finrank_frameSpace_eq :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ringKrullDim (S.A ⧸ (S.x0 ⊔ S.u.triM)) ≤ (2 * C₀ : ℕ) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨f, h1, h2, h3⟩ := frame_fiber_eq hF hn S (S.x0 ⊔ S.u.triM) le_sup_left
  letI : Algebra (ResidueField O) (S.A ⧸ (S.x0 ⊔ S.u.triM)) := f.toAlgebra
  have ht : (S.u.map (Ideal.Quotient.mk (S.x0 ⊔ S.u.triM))).triM = ⊥ := by
    refine Ideal.span_eq_bot.2 ?_
    rintro _ ⟨g, i, j, h, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.subset_span ⟨g, i, j, h, rfl⟩))
  obtain ⟨T, h4, h5⟩ := point hF hn _ _ h1 ht h2
  refine dim_gen (ResidueField O) _ T _ h4 (eq_top_iff.2 fun x _ => ?_)
  have h6 : Subring.closure (Set.range f ∪ {x | ∃ g i j, x = (S.u.map (Ideal.Quotient.mk (S.x0 ⊔ S.u.triM))).r g i j}) ≤
      (Algebra.adjoin (ResidueField O) (T : Set (S.A ⧸ (S.x0 ⊔ S.u.triM)))).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨g, i, j, rfl⟩)
    · exact Subalgebra.algebraMap_mem _ a
    · exact h5 g i j
  exact h6 (h3 ▸ Subring.mem_top x)
end
end
