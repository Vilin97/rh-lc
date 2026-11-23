module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAWStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceSimplicesOverSubCompositeStatement
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductNaturalInSheafComplexPairingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSheafComplexPairingTensorAssocDescStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTateTwistResolutionTensorFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTensorUniversalPropertyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionMapExistsUniqueHomotopyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUniqueStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductAssocOfPairingAssoc

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sum_range_triangle {A : Type*} [AddCommMonoid A] (G : ℕ → ℕ → A) (N : ℕ) :
    ∑ P ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (P + 1), G p (P - p) =
      ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), G p r := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨x.2, x.1 - x.2⟩) (fun y _ => ⟨y.1 + y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    rfl

theorem Sx.sub_congr {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) {j j' l : ℕ} (hj : j = j') (h : j + l ≤ N)
    (h' : j' + l ≤ N) : x.sub j l h = x.sub j' l h' := by
  subst hj
  rfl

theorem Pair.mul_ev_congr {R : Type} [CommRing R] {J K M : Cx R} (μ : Pair J K M) {E : Spc} {k : ℤ}
    (γ : Cochain ((chains R).obj E) K k) {U : Scheme.{0}} {N : ℕ} (x : Sx E N U) (t tu : ℤ) (b : Sec (J.X t) U)
    {a a' j j' : ℕ} (ha : a = a') (hj : j = j') (hx : j + a ≤ N) (hx' : j' + a' ≤ N)
    (h : t + (-(a : ℤ) + k) = tu) (h' : t + (-(a' : ℤ) + k) = tu) :
    μ.mul U t (-(a : ℤ) + k) tu h b (ev γ a _ rfl U (x.sub j a hx)) =
      μ.mul U t (-(a' : ℤ) + k) tu h' b (ev γ a' _ rfl U (x.sub j' a' hx')) := by
  subst ha hj
  rfl

end GlobalTheory.EtC

theorem GlobalTheory.EtC.Pair.cup_assoc_of_mul_assoc : ∀ (R : Type) [CommRing R] {I J K M M' L : Cx R} (μ : Pair I J M) (ν : Pair M K L) (μ' : Pair J K M') (ν' : Pair I M' L), (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c, ν.mul U st u w h2 (μ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) → ∀ (E : Spc) {n m k nm mk w : ℤ} (h1 : n + m = nm) (h2 : nm + k = w) (h3 : m + k = mk) (h4 : n + mk = w) a b c, ν.cup E h2 (μ.cup E h1 a b) c = ν'.cup E h4 a (μ'.cup E h3 b c) := by
  intro R _ I J K M M' L μ ν μ' ν' hA E n m k nm mk w h1 h2 h3 h4 a b c
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
  obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective c
  obtain ⟨δ, hδ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ h1).1 α β
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ h1).2 α β δ hδ]
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R ν h2).1 δ γ
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R ν h2).2 δ γ ε hε]
  obtain ⟨δ', hδ'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ' h3).1 β γ
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ' h3).2 β γ δ' hδ']
  obtain ⟨ε', hε'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R ν' h4).1 α δ'
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R ν' h4).2 α δ' ε' hε']
  suffices hh : ε.1 = ε'.1 by rw [show ε = ε' from Subtype.ext hh]
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := L) (n := w)).2.2.1
  intro N s hs U x
  rw [hε N s hs U x, hε' N s hs U x]
  have ss := fun {N' : ℕ} (y : Sx E N' U) => (GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite y).1
  let G : ℕ → ℕ → Sec (L.X s) U := fun p r => if hpr : p + r ≤ N then
    (((mk * (p : ℤ) + k * (r : ℤ)).negOnePow : ℤˣ) : ℤ) •
      ν'.mul U (-(p : ℤ) + n) (-((N - p : ℕ) : ℤ) + mk) s (by omega) (ev α.1 p _ rfl U (x.sub 0 p (by omega)))
        (μ'.mul U (-(r : ℤ) + m) (-((N - p - r : ℕ) : ℤ) + k) (-((N - p : ℕ) : ℤ) + mk) (by omega)
          (ev β.1 r _ rfl U (x.sub p r hpr)) (ev γ.1 (N - p - r) _ rfl U (x.sub (p + r) (N - p - r) (by omega))))
    else 0
  trans ∑ P ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (P + 1), G p (P - p)
  · rw [← Fin.sum_univ_eq_sum_range (fun P => ∑ p ∈ Finset.range (P + 1), G p (P - p)) (N + 1)]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hP := P.isLt

    rw [hδ (P : ℕ) _ _ U (x.sub 0 (P : ℕ) (by omega)), map_sum, LinearMap.sum_apply, Finset.smul_sum,
    ← Fin.sum_univ_eq_sum_range (fun p => G p ((P : ℕ) - p)) ((P : ℕ) + 1)]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp := p.isLt
    simp only [G]
    rw [dite_eq_left (by omega), Units.smul_def, Units.smul_def, map_zsmul, LinearMap.smul_apply, smul_smul,
      ← Units.val_mul, ← Int.negOnePow_add]
    rw [hA (tu := -((N - (p : ℕ) : ℕ) : ℤ) + mk)]
    rotate_left
    · omega
    · omega
    rw [ss, ss, GlobalTheory.EtC.Sx.sub_congr x (show 0 + 0 = 0 from rfl) _ (by omega),
      GlobalTheory.EtC.Sx.sub_congr x (show 0 + (p : ℕ) = p by omega) _ (by omega)]
    rw [GlobalTheory.EtC.Pair.mul_ev_congr μ' γ.1 x _ _ _ (a' := N - (p : ℕ) - ((P : ℕ) - (p : ℕ)))
      (j' := (p : ℕ) + ((P : ℕ) - (p : ℕ))) (by omega) (by omega) _ (by omega) _ (by omega)]
    have hsg : (k * ((P : ℕ) : ℤ) + m * ((p : ℕ) : ℤ)).negOnePow =
        (mk * ((p : ℕ) : ℤ) + k * (((P : ℕ) - (p : ℕ) : ℕ) : ℤ)).negOnePow := by
      congr 1
      rw [Nat.cast_sub (by omega), ← h3]
      ring
    rw [hsg]
  trans ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), G p r
  · exact GlobalTheory.EtC.sum_range_triangle G N
  rw [← Fin.sum_univ_eq_sum_range (fun p => ∑ r ∈ Finset.range (N - p + 1), G p r) (N + 1)]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.isLt

  rw [hδ' (N - (p : ℕ)) _ _ U (x.sub (p : ℕ) (N - (p : ℕ)) (by omega)), map_sum, Finset.smul_sum,
  ← Fin.sum_univ_eq_sum_range (fun r => G p r) (N - (p : ℕ) + 1)]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr := r.isLt
  simp only [G]
  rw [dite_eq_left (by omega), Units.smul_def, Units.smul_def, map_zsmul, smul_smul, ← Units.val_mul,
    ← Int.negOnePow_add, ss, ss]
  rfl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductAssocOfPairingAssocStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cupProduct_assoc_of_pairing_assoc : ∀ (R : Type) [CommRing R] {I J K M M' L : Cx R} (μ : Pair I J M) (ν : Pair M K L) (μ' : Pair J K M') (ν' : Pair I M' L), (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c, ν.mul U st u w h2 (μ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) → ∀ (E : Spc) {n m k nm mk w : ℤ} (h1 : n + m = nm) (h2 : nm + k = w) (h3 : m + k = mk) (h4 : n + mk = w) a b c, ν.cup E h2 (μ.cup E h1 a b) c = ν'.cup E h4 a (μ'.cup E h3 b c) := by
  first | exact @GlobalTheory.EtC.Pair.cup_assoc_of_mul_assoc | exact GlobalTheory.EtC.Pair.cup_assoc_of_mul_assoc | (intros; apply GlobalTheory.EtC.Pair.cup_assoc_of_mul_assoc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductAssoc

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.CupAssoc

def trPair {q : ℕ} {I J : Cx (ZMod q)} {k k' : ℤ} (h : k = k') (μ : Pair I J (res _ (tw q k))) :
    Pair I J (res _ (tw q k')) := h ▸ μ

theorem trPair_isTwPair {q : ℕ} {i j k k' : ℤ} (h : k = k') (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)))
    (hμ : IsTwPair μ) : IsTwPair (trPair h μ) := by
  subst h; exact hμ

theorem trPair_cup {q : ℕ} {I J : Cx (ZMod q)} {k k' : ℤ} (h : k = k') (μ : Pair I J (res _ (tw q k))) (E : Spc)
    {n m w : ℤ} (hw : n + m = w) (a : CohomologyClass ((chains _).obj E) I n) (b : CohomologyClass ((chains _).obj E) J m) :
    (trPair h μ).cup E hw a b = Ht.cast hw h (μ.cup E rfl a b) := by
  subst h; subst hw; rfl

theorem secMap_id {R : Type} [CommRing R] (K : Cx R) (s : ℤ) {U : Scheme.{0}} (x : Sec (K.X s) U) :
    Sec.map (HomologicalComplex.Hom.f (𝟙 K) s) x = x := rfl

theorem main : ∀ (q : ℕ) [NeZero q] (E : Spc) {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l),
    cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring) := by
  intro q _ E n m k i j l a b c
  have hk : i + (j + l) = i + j + l := by ring
  have hd : n + (m + k) = n + m + k := by ring

  set μ := twPair q i j with hμdef
  set P := twPair q (i + j) l with hPdef
  set μ' := twPair q j l with hμ'def
  set Q' := trPair hk (twPair q i (j + l)) with hQ'def
  have hμ : IsTwPair μ := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1
  have hP : IsTwPair P := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q (i + j) l).1
  have hμ' : IsTwPair μ' := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q j l).1
  have hQ' : IsTwPair Q' := trPair_isTwPair hk _ (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i (j + l)).1
  have hfun := GlobalTheory.EtC.ZcFun.main (ZMod q)
  have cpush_id : ∀ (K I : Cx (ZMod q)) (n : ℤ) x, cpush K (𝟙 I) n x = x := fun K I n x => ((hfun.1 K I n x).2)

  obtain ⟨hIi, hFi, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q i
  obtain ⟨hIj, hFj, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q j
  obtain ⟨hIl, hFl, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q l
  obtain ⟨-, -, hext⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q (i + j + l)
  obtain ⟨T, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  obtain ⟨T3, τ', hτ'⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) T (res _ (tw q l))
  have hT := GlobalTheory.T.isTateTwistResolution_tensor_flat q i j (i + j) rfl _ _ hIi hIj hFj τ hτ
  have hT3 := GlobalTheory.T.isTateTwistResolution_tensor_flat q (i + j) l (i + j + l) rfl _ _ hT hIl hFl τ' hτ'

  obtain ⟨u, hu, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ hτ).1 μ (𝟙 _) (𝟙 _)
  obtain ⟨u₁, hu₁, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ' hτ').1 P u (𝟙 _)
  have L1 : μ.cup E rfl a b = cpush _ u (n + m) (τ.cup E rfl a b) := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ μ (𝟙 _) (𝟙 _) u hu E rfl a b, cpush_id, cpush_id]
  have L2 : P.cup E rfl (cpush _ u (n + m) (τ.cup E rfl a b)) c = cpush _ u₁ (n + m + k) (τ'.cup E rfl (τ.cup E rfl a b) c) := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ' P u (𝟙 _) u₁ hu₁ E rfl _ c, cpush_id]

  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_sheafComplexPairing_tensor_assoc_desc (ZMod q) τ τ' hτ hτ' μ' Q'
  obtain ⟨u₂, hu₂, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ' hτ').1 ν (𝟙 _) (𝟙 _)
  have R1 : ν.cup E rfl (τ.cup E rfl a b) c = Q'.cup E hd a (μ'.cup E rfl b c) :=
    GlobalTheory.T.cupProduct_assoc_of_pairing_assoc (ZMod q) τ ν μ' Q' hν E rfl rfl rfl hd a b c
  have R2 : cpush _ u₂ (n + m + k) (τ'.cup E rfl (τ.cup E rfl a b) c) = ν.cup E rfl (τ.cup E rfl a b) c := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ' ν (𝟙 _) (𝟙 _) u₂ hu₂ E rfl _ c, cpush_id, cpush_id]

  have hgen : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (u₁.f 0) (τ'.mul U 0 0 0 (add_zero 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) (resGen l ζ)) =
      Sec.map (u₂.f 0) (τ'.mul U 0 0 0 (add_zero 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) (resGen l ζ)) := by
    intro U ζ
    rw [hu₁, hu₂]
    try simp only [secMap_id]
    rw [hu]
    try simp only [secMap_id]
    rw [hμ U ζ, hP U ζ, hν U 0 0 0 0 0 0 (add_zero 0) (add_zero 0) (add_zero 0) (add_zero 0), hμ' U ζ, hQ' U ζ]
  obtain ⟨hH⟩ := (hext _ hT3).2 u₁ u₂ hgen
  have hpush := ((hfun.2.2.2.2 u₁ u₂ ⟨hH⟩) ((chains _).obj E) (n + m + k)).2

  show P.cup E rfl (μ.cup E rfl a b) c = _
  rw [L1, L2, hpush, R2, R1, hQ'def, trPair_cup]
  rfl

end GlobalTheory.EtC.CupAssoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductAssocStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistCupProduct_assoc : ∀ (q : ℕ) [NeZero q] (E : Spc) {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l), cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring) := by
  first
  | exact @GlobalTheory.EtC.CupAssoc.main
  | exact GlobalTheory.EtC.CupAssoc.main
  | (intros; apply GlobalTheory.EtC.CupAssoc.main <;> assumption)
end
end
