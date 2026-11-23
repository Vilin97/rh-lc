module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetPowerSectionNeZeroDefiniteStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfA
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeBallNoContractionUnitaryUpperLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitInterpolationDetWeightFreeBallIndefiniteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelTrivialDefiniteNoContractionStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotallySplitPrimeUpperLevelUnipotent

section

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.LevelSplit

theorem primesOver_eq (E : Type) [Field E] [NumberField E] {g : ℕ} (hg : g.Prime) :
    (Ideal.span {(g : ℤ)}).primesOver (𝓞 E) = {P : Ideal (𝓞 E) | P.IsPrime ∧ (g : 𝓞 E) ∈ P} := by
  ext P
  simp only [Ideal.primesOver, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP, hL⟩
    refine ⟨hP, ?_⟩
    have h1 : (g : ℤ) ∈ Ideal.span {(g : ℤ)} := Ideal.mem_span_singleton_self _
    rw [hL.over] at h1
    simpa using (Ideal.mem_comap.mp h1)
  · rintro ⟨hP, hgP⟩
    refine ⟨hP, ⟨?_⟩⟩
    have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hg).irreducible
    refine hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simpa using hgP

end GlobalTheory.LevelSplit

theorem GlobalTheory.levelHyp_totallySplit_unipotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C), LevelHyp M → ∃ g : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g ∧ 3 * r < g ∧ ∀ c, ∀ β ∈ M.upper c, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver (M.comp c).L' g β := by
  intro E _ _ _ r U C _ _ M hM
  obtain ⟨g, ⟨hg, hcard⟩, hgr, hU⟩ := hM
  have hset := GlobalTheory.LevelSplit.primesOver_eq E hg
  refine ⟨g, ⟨hg, ?_⟩, hgr, ?_⟩
  · rw [hset]; exact hcard
  · intro c β hβ P hP
    rw [hset] at hP
    exact ⟨r, fun v hv => hU c β hβ P hP.1 hP.2 v hv⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotallySplitPrimeUpperLevelUnipotentStatement

section

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.exists_totallySplitPrime_upperLevel_unipotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C), LevelHyp M → ∃ g : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g ∧ 3 * r < g ∧ ∀ c, ∀ β ∈ M.upper c, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver (M.comp c).L' g β := by
  first | exact @GlobalTheory.levelHyp_totallySplit_unipotent | exact GlobalTheory.levelHyp_totallySplit_unipotent | (intros; apply GlobalTheory.levelHyp_totallySplit_unipotent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUpperLevelSubgroupComponent

section

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory

theorem upperLevel_isSubgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (c : C), ∃ G : Subgroup (GL (Fin r) E), (∀ β, β ∈ G ↔ β ∈ M.upper c) ∧ (M.comp c).Γ ≤ G := by
  intro E _ _ _ r U C _ _ M c
  have h1 : M.tr 1 c ∈ (M.comp c).Γ := by
    have h := M.tr_mul 1 1 c
    simp only [one_mul, one_smul] at h
    have h' : (M.tr 1 c)⁻¹ ∈ (M.comp c).Γ := by
      simpa [mul_inv_rev, mul_assoc] using h
    simpa using inv_mem h'
  refine ⟨{ carrier := M.upper c
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun β => Iff.rfl, ?_⟩
  · rintro a b ⟨u, hu, γ, hγ, rfl⟩ ⟨v, hv, γ', hγ', rfl⟩
    have hc := (M.tr_conj u c γ').1 hγ'
    rw [hu] at hc
    have hm := M.tr_mul u v c
    rw [mul_smul, hv, hu] at hm
    refine ⟨u * v, by rw [mul_smul, hv, hu], γ * (M.tr u c * γ' * (M.tr u c)⁻¹) *
      (M.tr (u * v) c * (M.tr u c * M.tr v c)⁻¹)⁻¹, ?_, ?_⟩
    · exact mul_mem (mul_mem hγ hc) (inv_mem hm)
    · group
  · exact ⟨1, one_smul _ _, (M.tr 1 c)⁻¹, inv_mem h1, by group⟩
  · rintro a ⟨u, hu, γ, hγ, rfl⟩
    have hu' : u⁻¹ • c = c := by rw [inv_smul_eq_iff, hu]
    have hm := M.tr_mul u⁻¹ u c
    rw [inv_mul_cancel, one_smul, hu] at hm
    have hw : M.tr u⁻¹ c * M.tr u c ∈ (M.comp c).Γ := by
      have := mul_mem (inv_mem h1) hm
      simpa [mul_assoc] using inv_mem this
    have hc := (M.tr_conj u⁻¹ c γ⁻¹).1 (inv_mem hγ)
    rw [hu'] at hc
    refine ⟨u⁻¹, hu', (M.tr u⁻¹ c * M.tr u c)⁻¹ * (M.tr u⁻¹ c * γ⁻¹ * (M.tr u⁻¹ c)⁻¹), ?_, ?_⟩
    · exact mul_mem (inv_mem hw) hc
    · group
  · intro γ hγ
    exact ⟨1, one_smul _ _, γ * (M.tr 1 c)⁻¹, mul_mem hγ (inv_mem h1), by group⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUpperLevelSubgroupComponentStatement

section

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.exists_upperLevel_subgroup_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (c : C), ∃ G : Subgroup (GL (Fin r) E), (∀ β, β ∈ G ↔ β ∈ M.upper c) ∧ (M.comp c).Γ ≤ G := by
  first | exact @GlobalTheory.upperLevel_isSubgroup | exact GlobalTheory.upperLevel_isSubgroup | (intros; apply GlobalTheory.upperLevel_isSubgroup <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelIsUnitaryStabiliserBothLattices

section

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.UpperStab

theorem upper_isUStab (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (c : C) :
    ∀ β ∈ M.upper c, IsUStab (M.comp c).Gm (M.comp c).L' β ∧ IsUStab (M.comp c).Gm (M.comp c).Λ β := by
  rintro β ⟨u, hu, γ, hγ, rfl⟩
  have hs := (M.comp c).Γ_stab γ hγ
  have hh : ∀ x y, herm (M.comp c).Gm (Matrix.mulVec ((γ * M.tr u c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x)
      (Matrix.mulVec ((γ * M.tr u c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) y) = herm (M.comp c).Gm x y := by
    intro x y
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs.1, M.comp_Gm c, M.tr_herm]
  refine ⟨⟨hh, fun v => ?_⟩, ⟨hh, fun v => ?_⟩⟩
  · have h1 := M.tr_L' u c v
    rw [hu] at h1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1]
    exact M.Γ_L' c γ hγ _
  · have h1 := M.tr_Λ u c v
    rw [hu] at h1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1]
    exact hs.2 _

end GlobalTheory.UpperStab
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelIsUnitaryStabiliserBothLatticesStatement

section

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.upperLevel_isUnitaryStabiliser_both_lattices : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (c : C), ∀ β ∈ M.upper c, IsUStab (M.comp c).Gm (M.comp c).L' β ∧ IsUStab (M.comp c).Gm (M.comp c).Λ β := by
  first | exact @GlobalTheory.UpperStab.upper_isUStab | exact GlobalTheory.UpperStab.upper_isUStab | (intros; apply GlobalTheory.UpperStab.upper_isUStab <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormNonzeroAtOneLift

section

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.LiftInterp

theorem zero_mem_SS {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) : (0 : Frame X.Ψ r → ℂ) ∈ X.SS la := by
  obtain ⟨⟨hz, -, -⟩, -⟩ := siegelSpaceAlgebra_holds r X la la 0
  exact hz

theorem bchar_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (la : Wt Ψ r) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  classical
  unfold bchar
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  intro h0
  apply (hb τ).1
  have hU : (mat b τ).IsUpperTriangular := fun a c hca => (hb τ).2 a c hca
  rw [Matrix.det_of_upperTriangular hU]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa [mat] using h0)

theorem comp_interp {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
    (hχ : ∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1) (G : Subgroup (GL (Fin r) E)) (g : ℕ)
    (hg : GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g) (hgr : 3 * r < g) (hΓG : X.Γ ≤ G)
    (hL' : ∀ γ ∈ G, IsUStab X.Gm X.L' γ) (hΛ : ∀ γ ∈ G, IsUStab X.Gm X.Λ γ)
    (hU : ∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) (s : ℕ) (hs : Even s)
    (hsb : 2 * r + 50 * r ^ 2 * (X.Ψ.card * (X.p0 * (r - X.p0))) + 1 ≤ s)
    (x : Frame X.Ψ r) (hx : x ∈ X.dom) (hNC : GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x) :
    ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → P (lact γ x) = 0 := by
  by_cases hdef : X.p0 = 0 ∨ X.p0 = r
  · have h1 := GlobalTheory.T.upperLevel_trivial_definite_noContraction E r X G g hg hgr hL' hU hdef x hx hNC
    obtain ⟨P, hP, hP0⟩ := GlobalTheory.T.exists_detPowerSection_ne_zero_definite E r X.toData (fun γ hγ => h1 γ (hΓG hγ)) hdef s x hx
    refine ⟨P, hP, hP0, fun γ hγ hγ' => absurd ?_ hγ'⟩
    rw [h1 γ hγ]
    exact X.Γ.one_mem
  · push_neg at hdef
    have hp0 : 0 < X.p0 := Nat.pos_of_ne_zero hdef.1
    have hp1 : X.p0 < r := lt_of_le_of_ne X.p0_le hdef.2
    obtain ⟨x0, h0, ⟨b, hb, rfl⟩, hFB⟩ := GlobalTheory.T.freeBall_noContraction_unitaryUpperLevel E r X G g hg hgr hΓG hL' hΛ hU x hx hNC
    obtain ⟨P, hP, hP0, hPγ⟩ := GlobalTheory.T.orbitInterpolation_detWeight_freeBall_indefinite E r X.toData hχ G x0 h0 hFB hp0 hp1 s hs hsb
    have hx0 : x0 ∈ X.dom := IW.orth_mem_dom X.toData x0 h0
    refine ⟨P, hP, ?_, fun γ hγ hγ' => ?_⟩
    · rw [hP.1.1.2.1 x0 hx0 b hb]
      exact mul_ne_zero (bchar_ne_zero _ hb) hP0
    · have hy : lact γ x0 ∈ X.dom := GlobalTheory.MajInv.lact_mem_dom X.toData (hΛ γ hγ) hx0
      rw [FundSetPf.lact_rmul, hP.1.1.2.1 _ hy b hb, hPγ γ hγ hγ', mul_zero]

theorem castFrame_symm_cast {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ')
    (y : Frame Ψ r) : castFrame h.symm (castFrame h y) = y := by
  subst h; rfl

theorem castFrame_lact {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ')
    (γ : GL (Fin r) E) (y : Frame Ψ r) : castFrame h (lact γ y) = lact γ (castFrame h y) := by
  subst h; rfl

theorem castFrame_mem_GG {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ')
    (G : Matrix (Fin r) (Fin r) E) (p : ℕ) (y : Frame Ψ' r) (hy : y ∈ GG Ψ' G p) :
    castFrame h.symm y ∈ GG Ψ G p := by
  subst h; exact hy

theorem castWt_deMul {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (p s : ℕ) :
    castWt h (deMul Ψ' r p s) = deMul Ψ r p s := by
  subst h; rfl

theorem exists_form_one_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), LevelHyp M → ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ s → ∀ (c : C) (x : Frame M.Ψ r), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction (M.comp c) (castFrame (M.comp_Ψ c).symm x) → x ∈ M.dom → ∃ u ∈ M.SS (deMul M.Ψ r M.p0 s), u c x ≠ 0 ∧ (∀ h : U, h ≠ 1 → M.pull h u c x = 0) ∧ ∀ c', (∀ h : U, h • c ≠ c') → ∀ y, u c' y = 0 := by
  intro E _ _ _ r U C _ _ _ _ M hLH s hs hsb c x hNC hx
  classical
  obtain ⟨g, hg, hgr, hUn⟩ := GlobalTheory.T.exists_totallySplitPrime_upperLevel_unipotent E r U C M hLH
  obtain ⟨G, hG, hΓG⟩ := GlobalTheory.T.exists_upperLevel_subgroup_component E r U C M c
  have hΨ : (M.comp c).Ψ = M.Ψ := M.comp_Ψ c
  have hx' : castFrame hΨ.symm x ∈ (M.comp c).dom := by
    have := castFrame_mem_GG hΨ M.Gm M.p0 x hx
    show castFrame hΨ.symm x ∈ GG (M.comp c).Ψ (M.comp c).Gm (M.comp c).p0
    rw [M.comp_Gm c, M.comp_basePoint c]
    exact this
  have hsb' : 2 * r + 50 * r ^ 2 * ((M.comp c).Ψ.card * ((M.comp c).p0 * (r - (M.comp c).p0))) + 1 ≤ s := by
    rw [hΨ, M.comp_basePoint c]; exact hsb
  obtain ⟨P, hP, hP0, hPγ⟩ := comp_interp (M.comp c) (M.χ_one c) G g hg hgr hΓG
    (fun β hβ => (GlobalTheory.T.upperLevel_isUnitaryStabiliser_both_lattices E r U C M c β ((hG β).1 hβ)).1) (fun β hβ => (GlobalTheory.T.upperLevel_isUnitaryStabiliser_both_lattices E r U C M c β ((hG β).1 hβ)).2)
    (fun β hβ => hUn c β ((hG β).1 hβ)) s hs hsb' _ hx' hNC
  let u : C → Frame M.Ψ r → ℂ := fun c' y => if c' = c then P (castFrame hΨ.symm y) else 0
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · intro c'
    by_cases hc : c' = c
    · subst hc
      have e : (fun y => u c' (castFrame (M.comp_Ψ c') y)) = P := by
        funext y
        simp only [u, if_pos rfl]
        exact congrArg P (castFrame_symm_cast _ y)
      rw [e, castWt_deMul]
      rw [M.comp_basePoint c'] at hP
      exact hP
    · have e : (fun y => u c' (castFrame (M.comp_Ψ c') y)) = 0 := by
        funext y
        simp [u, hc]
      rw [e]
      exact zero_mem_SS _ _
  · simpa [u] using hP0
  · intro h hh
    unfold TwoLevels.pull
    by_cases hc : h • c = c
    · simp only [u, hc, if_pos rfl]
      rw [castFrame_lact]
      refine hPγ _ ((hG _).2 ⟨h, hc, 1, (M.comp c).Γ.one_mem, by simp⟩) fun hm => hh ?_
      exact M.tr_faithful h c hc hm
    · simp [u, hc]
  · intro c' hc' y
    have hne : c' ≠ c := fun e => hc' 1 (by simp [e])
    simp [u, hne]

end GlobalTheory.LiftInterp
end
end
