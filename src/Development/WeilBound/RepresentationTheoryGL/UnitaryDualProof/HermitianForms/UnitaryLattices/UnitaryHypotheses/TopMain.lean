module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.HighestDerivProd
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.GlCongr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitarySemisimple
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.TwistedKernelFormsNonvanishing
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.UnipBLeColFixOne
import Mathlib.Algebra.Module.StablyFree.Basic

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.ExistsOrthOfFinset

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep

namespace PositivityTheory.RgUd.Form.U.Asm

theorem mem_fixed_iff_irr {G D : Type} [Group G] [AddCommGroup D] [Module ℂ D] (ρ : Representation ℂ G D)
    (K : Subgroup G) (v : D) : v ∈ fixed ρ K ↔ ∀ h : K, ρ (h : G) v = v := by
  change (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  simp

theorem exists_orth_of_finset {D : Type} [AddCommGroup D] [Module ℂ D] (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re) (s : Finset D) :
    ∀ u : D, ∃ w ∈ Submodule.span ℂ (s : Set D), ∀ m ∈ Submodule.span ℂ (s : Set D), B (u - w) m = 0 := by
  apply GlobalTheory.CompanionTheory.UnitSemisimple.exists_proj_finset <;> assumption

theorem exists_orth_decomp {G D : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup D]
    [Module ℂ D] (ρ : Representation ℂ G D) (hA : IsAdmissible ρ) (K₁ : Subgroup G) (hK₁o : IsOpen (K₁ : Set G))
    (hK₁c : IsCompact (K₁ : Set G)) (χ : G → ℝ) (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re)
    (hBe : ∀ g x y, B (ρ g x) (ρ g y) = (χ g : ℂ) * B x y) (W : Submodule ℂ D)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (u : D) :
    ∃ w ∈ W, ∀ w' ∈ W, B (u - w) w' = 0 := by
  classical
  by_cases hu : u = 0
  · exact ⟨0, W.zero_mem, fun w' _ => by simp [hu]⟩
  let S : Subgroup G :=
    { carrier := {g | ρ g u = u}
      mul_mem' := by
        intro a b (ha : ρ a u = u) (hb : ρ b u = u)
        show ρ (a * b) u = u
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by
        show ρ 1 u = u
        simp
      inv_mem' := by
        intro a (ha : ρ a u = u)
        show ρ a⁻¹ u = u
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSo : IsOpen (S : Set G) := hA.1 u
  let K : Subgroup G := K₁ ⊓ S
  have hKo : IsOpen (K : Set G) := by
    rw [Subgroup.coe_inf]; exact hK₁o.inter hSo
  have hKc : IsCompact (K : Set G) := by
    rw [Subgroup.coe_inf]; exact hK₁c.inter_right (Subgroup.isClosed_of_isOpen S hSo)
  have hKS : ∀ k : K, ρ (k : G) u = u := fun k => (Subgroup.mem_inf.1 k.2).2
  have hBu : B u u ≠ 0 := by
    intro h; have := hBp u hu; rw [h] at this; simp at this
  have hχ : ∀ k : K, (χ k : ℂ) = 1 := by
    intro k
    have h := hBe k u u
    rw [hKS k] at h
    have h2 : ((χ k : ℂ) - 1) * B u u = 0 := by rw [sub_mul, ← h]; ring
    rcases mul_eq_zero.1 h2 with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hBu
  have hBK : ∀ (k : K) x y, B (ρ (k : G) x) (ρ (k : G) y) = B x y := by
    intro k x y; rw [hBe, hχ, one_mul]
  have : FiniteDimensional ℂ (fixed ρ K) := hA.2 K hKo hKc
  let M : Submodule ℂ D := W ⊓ fixed ρ K
  have : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨s, hs⟩ : M.FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨w, hwM, hw⟩ := exists_orth_of_finset B hBp s u
  rw [hs] at hwM hw
  refine ⟨w, (Submodule.mem_inf.1 hwM).1, ?_⟩
  have huF : u - w ∈ fixed ρ K :=
    Submodule.sub_mem _ ((mem_fixed_iff_irr ρ K u).2 hKS) (Submodule.mem_inf.1 hwM).2
  have hfix := (mem_fixed_iff_irr ρ K _).1 huF
  intro w' hw'
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let f : K → D := fun k => ρ (k : G) w'
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro k0
    refine ⟨(fun k : K => (k0 : G)⁻¹ * (k : G)) ⁻¹' {g | ρ g w' = w'},
      (hA.1 w').preimage (continuous_const.mul continuous_subtype_val), ?_, ?_⟩
    · simp
    · intro k hk
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hk
      simp only [f]
      conv_lhs => rw [show (k : G) = (k0 : G) * ((k0 : G)⁻¹ * (k : G)) by group]
      rw [map_mul, Module.End.mul_apply, hk]
  obtain ⟨T, hTmem⟩ : ∃ T : Finset D, ∀ v, v ∈ T ↔ ∃ k : K, ρ (k : G) w' = v :=
    ⟨hf.range_finite.toFinset, fun v => by simp only [Set.Finite.mem_toFinset, Set.mem_range, f]⟩
  have hTst : ∀ h : K, ∀ v ∈ T, ρ (h : G) v ∈ T := by
    intro h v hv
    obtain ⟨k, rfl⟩ := (hTmem v).1 hv
    exact (hTmem _).2 ⟨h * k, by rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  have hinv : ∀ h : K, ∀ v, ρ ((h⁻¹ : K) : G) (ρ (h : G) v) = v := by
    intro h v
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hinv' : ∀ h : K, ∀ v, ρ (h : G) (ρ ((h⁻¹ : K) : G) v) = v := by
    intro h v
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hsumF : ∑ v ∈ T, v ∈ M := by
    refine Submodule.mem_inf.2 ⟨Submodule.sum_mem _ (fun v hv => ?_), ?_⟩
    · obtain ⟨k, rfl⟩ := (hTmem v).1 hv; exact hW _ _ hw'
    · rw [mem_fixed_iff_irr]
      intro h

      rw [map_sum]
      exact Finset.sum_nbij' (fun v => ρ (h : G) v) (fun v => ρ ((h⁻¹ : K) : G) v) (hTst h) (hTst h⁻¹)
        (fun v _ => hinv h v) (fun v _ => hinv' h v) (fun v _ => rfl)
  have h0 := hw _ hsumF

  rw [map_sum] at h0
  have hterm : ∀ v ∈ T, B (u - w) v = B (u - w) w' := by
    intro v hv
    obtain ⟨k, rfl⟩ := (hTmem v).1 hv
    conv_lhs => rw [← hfix k]
    exact hBK k _ _
  rw [Finset.sum_congr rfl hterm, Finset.sum_const] at h0
  have hcard : T.card ≠ 0 := Finset.card_ne_zero_of_mem ((hTmem w').2 ⟨1, by simp⟩)
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 hcard
  · exact h1

theorem irr_of_forms {G D : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup D] [Module ℂ D]
    [Nontrivial D] (ρ : Representation ℂ G D) (hA : IsAdmissible ρ) (K₁ : Subgroup G) (hK₁o : IsOpen (K₁ : Set G))
    (hK₁c : IsCompact (K₁ : Set G)) (χ : G → ℝ) (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBh : ∀ x y, B y x = starRingEnd ℂ (B x y)) (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re)
    (hBe : ∀ g x y, B (ρ g x) (ρ g y) = (χ g : ℂ) * B x y)
    (hC : ∀ C : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ, (∀ x y, C y x = starRingEnd ℂ (C x y)) → (∀ x, 0 ≤ (C x x).re) →
      (∀ x, (C x x).re ≤ (B x x).re) → (∀ g x y, C (ρ g x) (ρ g y) = (χ g : ℂ) * C x y) →
      ∃ c : ℂ, ∀ x y, C x y = c * B x y) :
    ρ.IsIrreducible := by
  classical
  have key : ∀ W : Subrepresentation ρ, W ≠ ⊥ → W = ⊤ := by
    intro W hWb
    let Wm : Submodule ℂ D := W.toSubmodule
    have hWs : ∀ g, ∀ w ∈ Wm, ρ g w ∈ Wm := fun g w hw => W.apply_mem_toSubmodule g hw
    let Wp : Submodule ℂ D :=
      { carrier := {x | ∀ w ∈ Wm, B x w = 0}
        add_mem' := by
          intro a b ha hb w hw
          rw [map_add (f := _), LinearMap.add_apply, ha w hw, hb w hw, add_zero]
        zero_mem' := by intro w _; simp
        smul_mem' := by
          intro c x hx w hw
          rw [map_smul, LinearMap.smul_apply, hx w hw, smul_zero] }
    have hWp : ∀ x, x ∈ Wp ↔ ∀ w ∈ Wm, B x w = 0 := fun x => Iff.rfl
    have hWps : ∀ g, ∀ x ∈ Wp, ρ g x ∈ Wp := by
      intro g x hx
      rw [hWp]
      intro w hw
      have h1 : ρ g (ρ g⁻¹ w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [← h1, hBe, (hWp x).1 hx _ (hWs _ _ hw), mul_zero]
    have hdec := fun u => exists_orth_decomp ρ hA K₁ hK₁o hK₁c χ B hBp hBe Wm hWs u
    have hcompl : IsCompl Wm Wp := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x hx hxp
        by_contra hne
        have := hBp x hne
        rw [(hWp x).1 hxp x hx] at this
        simp at this
      · rw [codisjoint_iff, eq_top_iff]
        intro u _
        obtain ⟨w, hw, hw'⟩ := hdec u
        rw [show u = w + (u - w) by abel]
        exact Submodule.add_mem_sup hw ((hWp _).2 hw')
    let P : D →ₗ[ℂ] D := Wm.projection Wp hcompl
    have hPW : ∀ x, P x ∈ Wm := fun x => Submodule.projection_apply_mem hcompl x
    have hPw : ∀ w ∈ Wm, P w = w := fun w hw => Submodule.projection_apply_of_mem_left hcompl hw
    have hPq : ∀ x, x - P x ∈ Wp := fun x => Submodule.sub_projection_mem hcompl x
    have hP0 : ∀ q ∈ Wp, P q = 0 := fun q hq => Submodule.projection_apply_of_mem_right hcompl hq
    have hPρ : ∀ g x, P (ρ g x) = ρ g (P x) := by
      intro g x
      have hx : ρ g x = ρ g (P x) + ρ g (x - P x) := by
        rw [← map_add (f := _)]; congr 1; abel
      rw [hx, map_add (f := _), hPw _ (hWs g _ (hPW x)), hP0 _ (hWps g _ (hPq x)), add_zero]
    let C : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ := (B ∘ₗ P).compl₂ P
    have hCapp : ∀ x y, C x y = B (P x) (P y) := fun x y => rfl
    have hBsplit : ∀ x, B x x = B (P x) (P x) + B (x - P x) (x - P x) := by
      intro x
      have h1 : B (x - P x) (P x) = 0 := (hWp _).1 (hPq x) _ (hPW x)
      have h2 : B (P x) (x - P x) = 0 := by rw [hBh (x - P x) (P x), h1, map_zero]
      conv_lhs => rw [show x = P x + (x - P x) by abel]
      simp only [map_add (f := _), LinearMap.add_apply, h1, h2, add_zero, zero_add]
    have hnn : ∀ x, 0 ≤ (B x x).re := by
      intro x
      by_cases h : x = 0
      · rw [h]; simp
      · exact (hBp _ h).le
    obtain ⟨c, hc⟩ := hC C (fun x y => by rw [hCapp, hCapp, hBh]) (fun x => by rw [hCapp]; exact hnn _)
      (fun x => by
        rw [hCapp, hBsplit x, Complex.add_re]
        have := hnn (x - P x)
        linarith)
      (fun g x y => by rw [hCapp, hCapp, hPρ, hPρ, hBe])
    obtain ⟨w0, hw0, hw0ne⟩ : ∃ w ∈ Wm, w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hWb
      apply Subrepresentation.toSubmodule_injective
      show Wm = ⊥
      exact (Submodule.eq_bot_iff _).2 hcon
    have hc1 : c = 1 := by
      have h := hc w0 w0
      rw [hCapp, hPw w0 hw0] at h
      have hB0 : B w0 w0 ≠ 0 := by
        intro h0; have := hBp w0 hw0ne; rw [h0] at this; simp at this
      have h2 : (c - 1) * B w0 w0 = 0 := by rw [sub_mul, ← h]; ring
      rcases mul_eq_zero.1 h2 with h1 | h1
      · exact sub_eq_zero.1 h1
      · exact absurd h1 hB0
    apply Subrepresentation.toSubmodule_injective
    show Wm = ⊤
    rw [eq_top_iff]
    intro x _
    have hq : x - P x = 0 := by
      by_contra hne
      have h := hc (x - P x) (x - P x)
      rw [hCapp, hc1, one_mul, hP0 _ (hPq x), map_zero] at h
      have := hBp _ hne
      rw [← h] at this
      simp at this
    have hx : x = P x := sub_eq_zero.1 hq
    rw [hx]
    exact hPW x
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : D)
    have h1 : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ D))
    rw [← h] at h1
    exact hx ((Submodule.mem_bot ℂ).1 (h1 : x ∈ (⊥ : Submodule ℂ D)))
  exact { exists_pair_ne := ⟨⊥, ⊤, hne⟩
          eq_bot_or_eq_top := fun W => by
            by_cases h : W = ⊥
            · exact Or.inl h
            · exact Or.inr (key W h) }

end PositivityTheory.RgUd.Form.U.Asm
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.TopMain

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Factor

variable {V D : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup D] [Module ℂ D]

theorem factor {C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hC : ∀ v w, C w v = starRingEnd ℂ (C v w)) (q : V →ₗ[ℂ] D)
    (hk : ∀ v ∈ LinearMap.ker q, ∀ w, C v w = 0) {v v' w w' : V} (hv : q v = q v') (hw : q w = q w') :
    C v w = C v' w' := by
  have h1 : v - v' ∈ LinearMap.ker q := by rw [LinearMap.mem_ker, map_sub, hv, sub_self]
  have h2 : w - w' ∈ LinearMap.ker q := by rw [LinearMap.mem_ker, map_sub, hw, sub_self]
  have e1 : C v w = C v' w := by
    have := hk _ h1 w
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have e2 : C v' w = C v' w' := by
    have := hk _ h2 v'
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    rw [hC w v', hC w' v', this]
  rw [e1, e2]

end Factor

theorem dpow_val (n : ℕ) (t : ℝ) (g : GL (Fin n) k) :
    ((dpow n t g : ℂˣ) : ℂ) = ((nabs k (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) := by
  simp only [dpow, detChar, MonoidHom.coe_comp, Function.comp_apply, absPow]
  rw [MonoidHom.coe_toHomUnits]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Complex.ofReal_cpow (nabs_pos k _).le]

theorem top_core {n N : ℕ} (h : n ≤ N) {V D : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup D] [Module ℂ D]
    [Nontrivial D] (π : Representation ℂ (GL (Fin N) k) V) (ρ : Representation ℂ (GL (Fin n) k) D)
    (hadm : IsAdmissible ρ) (q : V →ₗ[ℂ] D) (hqs : Function.Surjective q)
    (hqe : ∀ g v, q (π (blkAt k n N h g) v) = ρ g (q v)) (s t : ℝ) (hst : 2 * t + s = 0)
    (E : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hE1 : IsPsd E) (hE2 : ∀ v ∈ LinearMap.ker q, ∀ w, E v w = 0)
    (hE3 : ∀ v, E v v = 0 → v ∈ LinearMap.ker q)
    (hE4 : ∀ g v w, E (π (blkAt k n N h g) v) (π (blkAt k n N h g) w) =
      ((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * E v w)
    (hLift : ∀ C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, IsPsd C → (∀ v ∈ LinearMap.ker q, ∀ w, C v w = 0) →
      (∀ g v w, C (π (blkAt k n N h g) v) (π (blkAt k n N h g) w) =
        ((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * C v w) →
      (∀ v, (C v v).re ≤ (E v v).re) → ∃ c : ℂ, ∀ v w, C v w = c * E v w) :
    (twist ρ (dpow n t)).IsIrreducible ∧ IsUnitarisable (twist ρ (dpow n t)) := by
  obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective q (LinearMap.range_eq_top.2 hqs)
  have hqr : ∀ x, q (r x) = x := fun x => LinearMap.congr_fun hr x
  set Bt : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ := (E ∘ₗ r).compl₂ r with hBt
  have hBt_apply : ∀ x y, Bt x y = E (r x) (r y) := fun x y => rfl
  have hdesc : ∀ v w, Bt (q v) (q w) = E v w := fun v w => by
    rw [hBt_apply]
    exact factor hE1.1 q hE2 (hqr _) (hqr _)
  have hBh : ∀ x y, Bt y x = starRingEnd ℂ (Bt x y) := fun x y => by
    rw [hBt_apply, hBt_apply, hE1.1]
  have hBp : ∀ x, x ≠ 0 → 0 < (Bt x x).re := by
    intro x hx
    rw [hBt_apply]
    rcases (hE1.2 (r x)).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply hx
      have h0 : E (r x) (r x) = 0 := Complex.ext heq.symm (diag_real hE1.1 _)
      have := hE3 _ h0
      rw [LinearMap.mem_ker, hqr] at this
      exact this
  have hBe : ∀ g x y, Bt (ρ g x) (ρ g y) = ((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * Bt x y := by
    intro g x y
    obtain ⟨v, rfl⟩ := hqs x
    obtain ⟨w, rfl⟩ := hqs y
    rw [← hqe, ← hqe, hdesc, hdesc, hE4]
  refine ⟨?_, ⟨Bt, hBh, hBp, fun g x y => ?_⟩⟩
  · apply twist_irr
    obtain ⟨K₁, hK₁o, hK₁c, -⟩ := GlobalTheory.T.compact_open_subgroups_basis k n Set.univ Filter.univ_mem
    refine irr_of_forms ρ hadm K₁ hK₁o hK₁c (fun g => nabs k (GeneralLinearGroup.det g) ^ s) Bt hBh hBp hBe ?_
    intro Ct hCh hCp hCle hCe
    set C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := (Ct ∘ₗ q).compl₂ q with hC
    have hC_apply : ∀ v w, C v w = Ct (q v) (q w) := fun v w => rfl
    obtain ⟨c, hc⟩ := hLift C ⟨fun v w => by rw [hC_apply, hC_apply, hCh], fun v => by rw [hC_apply]; exact hCp _⟩
      (fun v hv w => by rw [hC_apply, LinearMap.mem_ker.1 hv, map_zero, LinearMap.zero_apply])
      (fun g v w => by rw [hC_apply, hC_apply, hqe, hqe, hCe])
      (fun v => by rw [hC_apply, ← hdesc]; exact hCle _)
    refine ⟨c, fun x y => ?_⟩
    obtain ⟨v, rfl⟩ := hqs x
    obtain ⟨w, rfl⟩ := hqs y
    rw [← hC_apply, hc, hdesc]
  · show Bt (((dpow n t g : ℂˣ) : ℂ) • ρ g x) (((dpow n t g : ℂˣ) : ℂ) • ρ g y) = Bt x y
    have hsm : ∀ (c : ℂ) (X Y : D), Bt (c • X) (c • Y) = c * (starRingEnd ℂ c * Bt X Y) := by
      intro c X Y
      rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul]
    rw [hsm, hBe, dpow_val, Complex.conj_ofReal]
    have hpos := nabs_pos k (GeneralLinearGroup.det g)
    have e : (nabs k (GeneralLinearGroup.det g) ^ t) * ((nabs k (GeneralLinearGroup.det g) ^ t) *
        (nabs k (GeneralLinearGroup.det g) ^ s)) = 1 := by
      rw [← Real.rpow_add hpos, ← Real.rpow_add hpos, show t + (t + s) = 0 by linarith, Real.rpow_zero]
    calc ((nabs k (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * (((nabs k (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) *
          (((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * Bt x y))
        = (((nabs k (GeneralLinearGroup.det g) ^ t) * ((nabs k (GeneralLinearGroup.det g) ^ t) *
          (nabs k (GeneralLinearGroup.det g) ^ s)) : ℝ) : ℂ) * Bt x y := by push_cast; ring
      _ = Bt x y := by rw [e]; simp

end PositivityTheory.RgUd.Form.U.Asm
end
end
end
