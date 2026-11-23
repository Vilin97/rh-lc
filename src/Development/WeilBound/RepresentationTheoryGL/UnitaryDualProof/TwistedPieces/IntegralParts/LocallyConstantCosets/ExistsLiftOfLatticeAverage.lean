module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.PsiBiUnion
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ContinuousLinearMat
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ValLeOneOfNabsLt
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ZpartUnique
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ContinuousOnZpart
public import GroundTheory.AutomorphicForms.WhittakerDistribution
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.Style
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.LcIndicator

section

@[expose] public section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem lc_indicator {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClopen S) (c : ℂ) :
    IsLocallyConstant (S.indicator fun _ => c) := by
  intro s
  by_cases h1 : c ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
  · convert isOpen_univ using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
  · convert hS.isOpen using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
  · convert hS.isClosed.isOpen_compl using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
  · convert isOpen_empty using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]

theorem psi_lift (hZ : CR Z) {A : Set (Matrix (Fin n) (Fin n) k)} (hAZ : A ⊆ Z) (hAc : IsCompact A)
    (hAo : ∀ a ∈ A, ∃ U : Set (Matrix (Fin n) (Fin n) k), IsOpen U ∧ a ∈ U ∧ U ∩ Z ⊆ A)
    {h : Sp k n → ℂ} (hh : h ∈ supportedIn (UU : Set (Sp k n))) :
    ∃ f ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z, f p = psi Z A h p := by
  classical
  haveI : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  haveI : T2Space (Matrix (Fin n) (Fin n) k) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  have hUU : IsOpen (UU : Set (Sp k n)) := isOpen_ne_fun continuous_snd continuous_const
  have hOU : OO Z ⊆ UU := fun p hp => hp.2
  have hhl : IsLocallyConstant h := (GroundTheory.Automorphic.mem_locallyConstantCompactSupport.1 hh.1).1
  have hhc : HasCompactSupport h := (GroundTheory.Automorphic.mem_locallyConstantCompactSupport.1 hh.1).2

  have hg1 : Continuous (fun p : OO Z => zpart Z (p : Sp k n).1) :=
    (continuousOn_zpart hZ).comp_continuous (continuous_fst.comp continuous_subtype_val) fun p => p.2.1
  have hg2 : Continuous (fun p : OO Z => (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2) : Sp k n)) :=
    ((continuous_fst.comp continuous_subtype_val).sub hg1).prodMk (continuous_snd.comp continuous_subtype_val)

  set S : Set (OO Z) := {p | zpart Z (p : Sp k n).1 ∈ A} with hSdef
  have hSc : IsClosed S := hAc.isClosed.preimage hg1
  have hSo : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨U, hU, hpU, hUA⟩ := hAo _ hp
    refine ⟨(fun q : OO Z => zpart Z (q : Sp k n).1) ⁻¹' U, fun q hq => hUA ⟨hq, (zpart_spec q.2.1).1⟩,
      hU.preimage hg1, hpU⟩
  have hphi : (fun p : OO Z => psi Z A h p) =
      fun p => S.indicator (fun _ => (1 : ℂ)) p * h (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2)) := by
    funext p
    rw [psi_of_mem p.2.1]
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show zpart Z (p : Sp k n).1 ∈ A from hp)]; rfl
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show zpart Z (p : Sp k n).1 ∉ A from hp)]

  have hsupp_cl : IsClosed (Function.support h) := by
    have : Function.support h = (h ⁻¹' {0})ᶜ := by ext x; simp [Function.mem_support]
    rw [this]
    exact (hhl.isOpen_fiber 0).isClosed_compl
  have hts : tsupport h ⊆ UU := by
    rw [tsupport, hsupp_cl.closure_eq]; exact hh.2

  set K : Set (Matrix (Fin n) (Fin n) k × Sp k n) := A ×ˢ (tsupport h ∩ (NB Z ×ˢ Set.univ)) with hK
  have hKc : IsCompact K := hAc.prod (hhc.inter_right ((isClosed_NB Z).prod isClosed_univ))
  set Φ : Matrix (Fin n) (Fin n) k × Sp k n → Sp k n := fun aq => (aq.1 + aq.2.1, aq.2.2) with hΦ
  have hΦc : Continuous Φ := (continuous_fst.add (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd)
  have hΦO : Φ '' K ⊆ OO Z := by
    rintro _ ⟨⟨a, q⟩, ⟨ha, hq, hqN⟩, rfl⟩
    have h2 : q.2 ≠ 0 := hts hq
    exact ⟨(cc_of_NB hZ (hAZ ha) hqN.1).1, h2⟩
  set Kc : Set (OO Z) := (Subtype.val : OO Z → Sp k n) ⁻¹' (Φ '' K) with hKcdef
  have hKcc : IsCompact Kc := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe,
      Set.inter_eq_left.2 hΦO]
    exact hKc.image hΦc
  have hsub : Function.support (fun p : OO Z => psi Z A h p) ⊆ Kc := by
    intro p hp
    rw [hphi, Function.mem_support] at hp
    have hpS : p ∈ S := by
      by_contra hn; rw [Set.indicator_of_notMem hn, zero_mul] at hp; exact hp rfl
    have hq : h (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2)) ≠ 0 := by
      rw [Set.indicator_of_mem hpS, one_mul] at hp; exact hp
    refine ⟨(zpart Z (p : Sp k n).1, (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2))),
      ⟨hpS, subset_tsupport _ hq, sub_mem_NB hZ p.2.1, Set.mem_univ _⟩, ?_⟩
    simp only [hΦ, add_sub_cancel]
  obtain ⟨f, hf, hfe⟩ := GroundTheory.Automorphic.Whittaker.exists_lift hUU hOU (φ := fun p : OO Z => psi Z A h p) (by
    rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport]
    refine ⟨?_, ?_⟩
    · rw [hphi]
      exact IsLocallyConstant.comp₂ (lc_indicator ⟨hSc, hSo⟩ 1) (hhl.comp_continuous hg2) (· * ·)
    · exact IsCompact.of_isClosed_subset hKcc isClosed_closure (closure_minimal hsub hKcc.isClosed))
  exact ⟨f, hf, fun p hp => hfe ⟨p, hp⟩⟩

end PositivityTheory.RgUd.TP.Nil.Fib2

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.PsiCosets

section

@[expose] public section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem psi_cosets {L M : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hL : IsLat Z L) (hM : IsLat Z M) (hML : M ≤ L) :
    ∃ D : Finset (Matrix (Fin n) (Fin n) k), D.card = M.relIndex L ∧ (∀ d ∈ D, d ∈ L) ∧
      ∀ h : Sp k n → ℂ, psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h =
        ∑ d ∈ D, psi Z ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))) h := by
  classical
  have hfi : (M.addSubgroupOf L).FiniteIndex := ⟨lat_index_pos hL hM hML⟩
  haveI : Fintype (L ⧸ M.addSubgroupOf L) := Fintype.ofFinite _
  let f : (L ⧸ M.addSubgroupOf L) → Matrix (Fin n) (Fin n) k := fun q => ((Quotient.out q : L) : Matrix (Fin n) (Fin n) k)
  have hf : Function.Injective f := fun a b hab => Quotient.out_inj.1 (Subtype.ext hab)
  have hmem : ∀ z q, z ∈ (fun a => a + f q) '' (M : Set (Matrix (Fin n) (Fin n) k)) ↔ z - f q ∈ M := by
    intro z q
    constructor
    · rintro ⟨m, hm, rfl⟩
      simpa using hm
    · intro hz
      exact ⟨z - f q, hz, by simp⟩
  have key : ∀ z, (L : Set (Matrix (Fin n) (Fin n) k)).indicator (1 : Matrix (Fin n) (Fin n) k → ℂ) z =
      ∑ d ∈ Finset.univ.image f, ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))).indicator 1 z := by
    intro z
    rw [Finset.sum_image (fun a _ b _ hab => hf hab)]
    by_cases hz : z ∈ L
    · rw [Set.indicator_of_mem (show z ∈ (L : Set (Matrix (Fin n) (Fin n) k)) from hz)]
      have hq : ∀ q, ((fun a => a + f q) '' (M : Set (Matrix (Fin n) (Fin n) k))).indicator
          (1 : Matrix (Fin n) (Fin n) k → ℂ) z =
          if (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) = q then 1 else 0 := by
        intro q
        have e : z - f q ∈ M ↔ (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) =
            QuotientAddGroup.mk (Quotient.out q) := by
          rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
          show z - f q ∈ M ↔ -z + f q ∈ M
          rw [show -z + f q = -(z - f q) by abel, neg_mem_iff]
        rw [QuotientAddGroup.out_eq'] at e
        by_cases h : (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) = q
        · rw [if_pos h, Set.indicator_of_mem ((hmem z q).2 (e.2 h))]
          rfl
        · rw [if_neg h, Set.indicator_of_notMem (fun h' => h (e.1 ((hmem z q).1 h')))]
      simp only [hq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rfl
    · rw [Set.indicator_of_notMem (show z ∉ (L : Set (Matrix (Fin n) (Fin n) k)) from hz)]
      symm
      apply Finset.sum_eq_zero
      intro q _
      apply Set.indicator_of_notMem
      intro h'
      apply hz
      have h2 : z = (z - f q) + f q := by abel
      rw [h2]
      exact L.add_mem (hML ((hmem z q).1 h')) (Quotient.out q).2
  refine ⟨Finset.univ.image f, ?_, ?_, fun h => funext fun p => ?_⟩
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl
  · intro d hd
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hd
    exact (Quotient.out q).2
  · rw [Finset.sum_apply]
    by_cases hp : p.1 ∈ CC Z
    · simp only [psi, Set.indicator_of_mem (show p ∈ {q : Sp k n | q.1 ∈ CC Z} from hp)]
      rw [key, Finset.sum_mul]
    · simp only [psi, Set.indicator_of_notMem (show p ∉ {q : Sp k n | q.1 ∈ CC Z} from hp), Finset.sum_const_zero]

end PositivityTheory.RgUd.TP.Nil.Fib2

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.ExistsLiftOfLatticeAverage

section

@[expose] public section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem comp_mem {e : Sp k n ≃ₜ Sp k n} (he : ∀ p, (e p).2 ≠ 0 → p.2 ≠ 0) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn (UU : Set (Sp k n))) : (fun p => f (e p)) ∈ supportedIn (UU : Set (Sp k n)) := by
  obtain ⟨⟨hlc, hcs⟩, hsu⟩ := hf
  refine ⟨⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩, ?_⟩
  intro p hp
  exact he p (hsu hp)

theorem comp_mem_univ {e : Sp k n ≃ₜ Sp k n} {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) : (fun p => f (e p)) ∈ supportedIn (Set.univ : Set (Sp k n)) := by
  obtain ⟨⟨hlc, hcs⟩, -⟩ := hf
  exact ⟨⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩, Set.subset_univ _⟩

def trH (c : Matrix (Fin n) (Fin n) k) : Sp k n ≃ₜ Sp k n := Homeomorph.addRight ((c, 0) : Sp k n)

theorem trH_apply (c : Matrix (Fin n) (Fin n) k) (p : Sp k n) : trH c p = tr c p :=
  Prod.ext rfl (add_zero p.2)

def homH (t : kˣ) : Sp k n ≃ₜ Sp k n :=
  Homeomorph.prodCongr (Homeomorph.smulOfNeZero (t : k) t.ne_zero) (Homeomorph.refl _)

def actH (g : GL (Fin n) k) : Sp k n ≃ₜ Sp k n where
  toFun := act g
  invFun := act g⁻¹
  left_inv p := Prod.ext (by simp [act, mul_assoc]) (by simp [act, Matrix.mulVec_mulVec])
  right_inv p := Prod.ext (by simp [act, mul_assoc]) (by simp [act, Matrix.mulVec_mulVec])
  continuous_toFun := by
    unfold act
    exact ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).prodMk
      (continuous_const.matrix_mulVec continuous_snd)
  continuous_invFun := by
    unfold act
    exact ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).prodMk
      (continuous_const.matrix_mulVec continuous_snd)

theorem tr_mem {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) (c : Matrix (Fin n) (Fin n) k) :
    (fun p => f (tr c p)) ∈ supportedIn (UU : Set (Sp k n)) := by
  have key := comp_mem (e := trH c) (fun p hp => by simpa [trH_apply, tr] using hp) hf
  simpa [trH_apply] using key

theorem hom_mem {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) (t : kˣ) :
    (fun p => f (hom t p)) ∈ supportedIn (UU : Set (Sp k n)) :=
  comp_mem (e := homH t) (fun p hp => hp) hf

theorem act_mem {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) (g : GL (Fin n) k) :
    (fun p => f (act g p)) ∈ supportedIn (UU : Set (Sp k n)) := by
  refine comp_mem (e := actH g) (fun p hp h0 => hp ?_) hf
  show g.val *ᵥ p.2 = 0
  rw [h0, Matrix.mulVec_zero]

def Good (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  TranslInv Z ζ ∧ SuppU ζ (CC Z ×ˢ Set.univ)

theorem agree {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hs : SuppU ζ (CC Z ×ˢ Set.univ)) {f f' : Sp k n → ℂ}
    (hf : f ∈ supportedIn (UU : Set (Sp k n))) (hf' : f' ∈ supportedIn (UU : Set (Sp k n)))
    (h : ∀ p ∈ OO Z, f p = f' p) : ζ f = ζ f' := by
  have hsub : f - f' ∈ supportedIn (UU : Set (Sp k n)) := Submodule.sub_mem _ hf hf'
  have hz := hs (f - f') hsub (by
    rintro p ⟨hp1, -⟩
    by_cases hp2 : p.2 = 0
    · have h1 : f p = 0 := by
        by_contra hne
        exact hf.2 hne hp2
      have h2 : f' p = 0 := by
        by_contra hne
        exact hf'.2 hne hp2
      simp [h1, h2]
    · simp [h ⟨p.1, p.2⟩ ⟨hp1, hp2⟩])
  rw [map_sub, sub_eq_zero] at hz
  exact hz

theorem good_tr {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hg : Good Z ζ) {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z)
    {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) : ζ (fun p => f (tr c p)) = ζ f := by
  exact hg.1 c hc f ⟨hf.1, Set.subset_univ _⟩

theorem coset_ok {M : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hM : IsLat Z M) {c : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) :
    (fun a => a + c) '' (M : Set (Matrix (Fin n) (Fin n) k)) ⊆ Z ∧
      IsCompact ((fun a => a + c) '' (M : Set (Matrix (Fin n) (Fin n) k))) ∧
      ∀ a ∈ (fun a => a + c) '' (M : Set (Matrix (Fin n) (Fin n) k)), ∃ U : Set (Matrix (Fin n) (Fin n) k),
        IsOpen U ∧ a ∈ U ∧ U ∩ Z ⊆ (fun a => a + c) '' (M : Set (Matrix (Fin n) (Fin n) k)) := by
  refine ⟨?_, hM.cpt.image (continuous_id.add continuous_const), ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact Z.add_mem (hM.sub hm) hc
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨U0, hU0, h0, hU0Z⟩ := hM.nhd
    have hmZ : m + c ∈ Z := Z.add_mem (hM.sub hm) hc
    refine ⟨(fun x => x - (m + c)) ⁻¹' U0, hU0.preimage (continuous_sub_right _), by simpa using h0, ?_⟩
    rintro x ⟨hxU, hxZ⟩
    have hxM : x - (m + c) ∈ M := hU0Z ⟨hxU, Z.sub_mem hxZ hmZ⟩
    refine ⟨x - (m + c) + m, M.add_mem hxM hm, ?_⟩
    show x - (m + c) + m + c = x
    abel

theorem lift_ex (hZ : CR Z) {M : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hM : IsLat Z M) {c : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) {h : Sp k n → ℂ} (hh : h ∈ supportedIn (UU : Set (Sp k n))) :
    ∃ f ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z,
      f p = psi Z ((fun a => a + c) '' (M : Set (Matrix (Fin n) (Fin n) k))) h p := by
  obtain ⟨h1, h2, h3⟩ := coset_ok hM hc
  exact psi_lift hZ h1 h2 h3 hh

theorem image_add_zero (M : Set (Matrix (Fin n) (Fin n) k)) : (fun a => a + (0 : Matrix (Fin n) (Fin n) k)) '' M = M := by
  simp

theorem exists_lift_of_lattice_average (hZ : CR Z) {M : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hM : IsLat Z M) {h : Sp k n → ℂ}
    (hh : h ∈ supportedIn (UU : Set (Sp k n))) :
    ∃ f ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z, f p = psi Z (M : Set (Matrix (Fin n) (Fin n) k)) h p := by
  have key := lift_ex hZ hM (c := 0) Z.zero_mem hh
  rwa [image_add_zero] at key

theorem tr_OO (hZ : CR Z) {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) {p : Sp k n} (hp : p ∈ OO Z) : tr c p ∈ OO Z :=
  ⟨(cc_add hZ hc).1.2 hp.1, hp.2⟩

theorem ind (hZ : CR Z) {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hg : Good Z ζ) {L M : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) (hM : IsLat Z M) (hML : M ≤ L) {h : Sp k n → ℂ} (hh : h ∈ supportedIn (UU : Set (Sp k n)))
    {fL fM : Sp k n → ℂ} (hfL : fL ∈ supportedIn (UU : Set (Sp k n))) (hfM : fM ∈ supportedIn (UU : Set (Sp k n)))
    (eL : ∀ p ∈ OO Z, fL p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p)
    (eM : ∀ p ∈ OO Z, fM p = psi Z (M : Set (Matrix (Fin n) (Fin n) k)) h p) :
    ζ fL = (M.relIndex L : ℂ) * ζ fM := by
  obtain ⟨D, hcard, hDL, hpsi⟩ := psi_cosets hL hM hML
  have hlift : ∀ d ∈ D, ∃ f ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z,
      f p = psi Z ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))) h p :=
    fun d hd => lift_ex hZ hM (hL.sub (hDL d hd)) hh
  choose! F hFmem hFeq using hlift
  have hsum : ζ fL = ζ (∑ d ∈ D, F d) := by
    refine agree hg.2 hfL (Submodule.sum_mem _ fun d hd => hFmem d hd) ?_
    intro p hp
    rw [eL p hp, hpsi h, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun d hd => (hFeq d hd p hp).symm
  have hterm : ∀ d ∈ D, ζ (F d) = ζ fM := by
    intro d hd
    have hcZ : d ∈ Z := hL.sub (hDL d hd)
    have e1 : ∀ p, psi Z (M : Set (Matrix (Fin n) (Fin n) k)) h p =
        psi Z ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))) h (tr d p) := by
      intro p
      have key := congrFun (psi_tr hZ ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))) h hcZ) p
      rw [key, Set.image_image]
      simp only [add_sub_cancel_right, Set.image_id']
    have e2 : ζ fM = ζ (fun p => F d (tr d p)) := by
      refine agree hg.2 hfM (tr_mem (hFmem d hd) d) ?_
      intro p hp
      rw [eM p hp, hFeq d hd _ (tr_OO hZ hcZ hp), e1]
    rw [e2, good_tr hg hcZ (hFmem d hd)]

  rw [hsum, map_sum, Finset.sum_congr rfl hterm, Finset.sum_const, hcard, nsmul_eq_mul]

theorem scale (hZ : CR Z) {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hg : Good Z ζ) {L : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) {t : kˣ} (ht : nabs k t < 1) {h : Sp k n → ℂ} (hh : h ∈ supportedIn (UU : Set (Sp k n)))
    {f f' : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) (hf' : f' ∈ supportedIn (UU : Set (Sp k n)))
    (e : ∀ p ∈ OO Z, f p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p)
    (e' : ∀ p ∈ OO Z, f' p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) (fun q => h (hom t q)) p) :
    ζ (fun p => f (hom t p)) = (((nabs k t)⁻¹ ^ Module.finrank k Z : ℝ) : ℂ) * ζ f' := by
  have hL' : IsLat Z (t⁻¹.val • L) := isLat_smul hL t⁻¹
  have hle : L ≤ t⁻¹.val • L := lat_le_inv hL ht
  have hh' : (fun q => h (hom t q)) ∈ supportedIn (UU : Set (Sp k n)) := hom_mem hh t
  have hg' : (fun p => f (hom t p)) ∈ supportedIn (UU : Set (Sp k n)) := hom_mem hf t
  have eg : ∀ p ∈ OO Z, (fun p => f (hom t p)) p =
      psi Z ((t⁻¹.val • L : AddSubgroup (Matrix (Fin n) (Fin n) k)) : Set (Matrix (Fin n) (Fin n) k))
        (fun q => h (hom t q)) p := by
    intro p hp
    have hp' : hom t p ∈ OO Z := ⟨(cc_smul hZ (t : k) hp.1).1, hp.2⟩
    have key := congrFun (psi_hom hZ (L : Set (Matrix (Fin n) (Fin n) k)) h t) p
    simp only at key ⊢
    rw [e _ hp', key, AddSubgroup.coe_pointwise_smul]
  have main := ind hZ hg hL' hL hle hh' hg' hf' eg e'
  rw [main]
  congr 1
  rw [← lat_index_smul hL t ht]
  push_cast
  rfl

end PositivityTheory.RgUd.TP.Nil.Fib2

end
end
end
