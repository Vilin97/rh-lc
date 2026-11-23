module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWU4OfLimWU3
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitRep
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRepStatement
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicLevelAwayNonsplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlowUpFibreSemilocal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClosedAtL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatUOfUnderEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobOpsIdx
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsExist
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TraceLimits.ExistsTraceLimit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TraceLimits.SlopeTestRemainingChoices
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerOfLinApprox

section

@[expose] public section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem ker_of_linApprox : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l))
    (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), IsSSRep r → LinApprox r C → ∀ s : Γ, (∀ ρ ∈ C, ρ s = 1) → r s = 1 := by
  intro l _ Γ _ a r C hss hC s hs
  have htr : ∀ g, trc r (s * g) = trc r g := by
    intro g
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨t, c, ht, hb⟩ := hC (ε / 2) (by positivity)
    have hsum : ∑ ρ ∈ t, c ρ * trc ρ (s * g) = ∑ ρ ∈ t, c ρ * trc ρ g := by
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      simp [trc, map_mul, hs ρ (ht hρ)]
    rw [dist_eq_norm]
    calc ‖trc r (s * g) - trc r g‖
        = ‖(trc r (s * g) - ∑ ρ ∈ t, c ρ * trc ρ (s * g)) - (trc r g - ∑ ρ ∈ t, c ρ * trc ρ g)‖ := by
          rw [hsum]; congr 1; ring
      _ ≤ ‖trc r (s * g) - ∑ ρ ∈ t, c ρ * trc ρ (s * g)‖ + ‖trc r g - ∑ ρ ∈ t, c ρ * trc ρ g‖ := norm_sub_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add (hb _) (hb _)
      _ = ε := by ring
  set R : Γ → Matrix (Fin a) (Fin a) (PadicAlgCl l) := fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) with hR
  have hM : R s - 1 ∈ Submodule.span (PadicAlgCl l) (Set.range R) := by
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨s, rfl⟩) ?_
    have : R 1 = 1 := by simp [hR]
    rw [← this]; exact Submodule.subset_span ⟨1, rfl⟩
  have h0 := GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep (PadicAlgCl l) Γ a r hss (R s - 1) hM (fun g => by
    have := htr g
    simp only [trc, map_mul, Units.val_mul] at this
    rw [sub_mul, one_mul, Matrix.trace_sub]
    simpa [hR] using sub_eq_zero.2 this)
  ext i j
  have := congrFun (congrFun (sub_eq_zero.1 h0) i) j
  simpa [hR] using this

end GlobalTheory.Cong
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinApproxOfPolyApproxTrc

section

@[expose] public section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem linApprox_of_polyApprox_trc : ∀ (k Γ : Type) [NormedField k] [IsUltrametricDist k] [Group Γ] (a : ℕ)
    (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k)), PolyApprox (trc r) (trc '' C) → LinApprox r C := by
  intro k Γ _ _ _ a r C h ε hε
  classical
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  let f : (Γ → k) → (Γ →* GL (Fin a) k) := Function.invFunOn trc C
  have hf : ∀ η ∈ s, f η ∈ C ∧ trc (f η) = η := fun η hη =>
    ⟨Function.invFunOn_mem (hs hη), Function.invFunOn_eq (hs hη)⟩
  have hinj : Set.InjOn f (s : Set (Γ → k)) := fun x hx y hy hxy => by
    rw [← (hf x hx).2, ← (hf y hy).2, hxy]
  refine ⟨s.image f, fun ρ => c (trc ρ), ?_, fun g => ?_⟩
  · intro ρ hρ
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hρ)
    exact (hf η hη).1
  · have := hP (MvPolynomial.X g)
    simp only [MvPolynomial.aeval_X] at this
    rw [Finset.sum_image hinj]
    have e : ∑ x ∈ s, c (trc (f x)) * trc (f x) g = ∑ η ∈ s, c η * η g :=
      Finset.sum_congr rfl fun η hη => by rw [(hf η hη).2]
    rw [e]
    exact this

end GlobalTheory.Cong
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApartOfNotMem

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.Cong.OffTLimit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem apart_of_not_mem {w₀ w : HeightOneSpectrum (𝓞 E)} (h₀ : ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal)
    (hw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : Apart w w₀ := by
  intro h
  apply hw
  have h1 : ((l : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ (w₀.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]; exact h₀
  rw [← h, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem z_eq_of_equiv {ι : Qbar l ≃+* ℂ} {Kw : Levels E a} {J : Type} (O : LocOps l ι Kw J) (j : J)
    {σ σ' : SmIrr (GL (Fin a) ((O.pl j).adicCompletion E))} (e : σ.ρ.Equiv σ'.ρ)
    (hne : PRep.fixed σ.ρ (Kw (O.pl j)) ≠ ⊥) : O.z j σ = O.z j σ' := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
  have he : ∀ g u, e.toLinearEquiv (σ.ρ g u) = σ'.ρ g (e.toLinearEquiv u) := fun g u =>
    LinearMap.congr_fun (e.isIntertwining' g) u
  have hv' : e.toLinearEquiv v ∈ PRep.fixed σ'.ρ (Kw (O.pl j)) := by
    change ∀ h : Kw (O.pl j), σ'.ρ (h : GL (Fin a) ((O.pl j).adicCompletion E)) (e.toLinearEquiv v) =
      ((1 : Kw (O.pl j) →* ℂˣ) h : ℂ) • e.toLinearEquiv v
    intro h
    have := hv h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at this ⊢
    rw [← he, this]
  have hop : e.toLinearEquiv (opOf σ.ρ (O.f j) v) = opOf σ'.ρ (O.f j) (e.toLinearEquiv v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [opOf, Finsupp.sum, map_sum, map_smul, he]
  have h2 := O.act j σ' _ hv'
  rw [← hop, O.act j σ v hv, map_smul] at h2
  have hne' : e.toLinearEquiv v ≠ 0 := by simpa using hv0
  exact smul_left_injective ℂ hne' h2

end GlobalTheory.Cong.OffTLimit

namespace GlobalTheory.Cong

end GlobalTheory.Cong
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LimWUOfSeeds

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.CongL

theorem overPl_unique {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (τ : E →+* ℂ)
    {w u : HeightOneSpectrum (𝓞 E)} (hw : OverPl ι τ w) (hu : OverPl ι τ u) : u = w := by
  by_contra hne
  have hI : u.asIdeal ≠ w.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have htop : u.asIdeal ⊔ w.asIdeal = ⊤ := Ideal.IsMaximal.coprime_of_ne u.isMaximal w.isMaximal hI
  have h1 : (1 : 𝓞 E) ∈ u.asIdeal ⊔ w.asIdeal := htop ▸ Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
  have hx' := hu x hx
  have hy' := hw y hy
  have hsum : ι.symm (τ ((x : E))) + ι.symm (τ ((y : E))) = 1 := by
    rw [← map_add (f := _), ← map_add (f := _)]
    have : ((x : E) + (y : E)) = 1 := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hxy
    rw [this, map_one, map_one]
  have hle := IsUltrametricDist.norm_add_le_max (ι.symm (τ ((x : E)))) (ι.symm (τ ((y : E))))
  rw [hsum, norm_one] at hle
  exact absurd hle (not_le.mpr (max_lt hx' hy'))

end GlobalTheory.CongL
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TraceLimits.LimFinOddOf

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace UpperTheory.Gal.Lim


open GlobalTheory.Cong.OffTLimit GlobalTheory.CongL.UnitLim in
theorem limWU4_of : ∀ (Rk : ℕ → Prop) (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (Wt : SeedWtU),
    SeedWU4 Rk Ty Gen Wt → CongUW4 Rk Ty Gen Wt → LimWU4 Rk := by
  intro Rk Ty Gen Wt hSd hC E Ω _ _ _ _ _ _ l _ ι a ha hRk d hF T hT U hU w₀ v' hw₀ hsp₀ hv' hspv hvap
  have hS : SphOps := GlobalTheory.Cong.SphOpsProof.sphOps
  classical
  have hl : l.Prime := Fact.out
  obtain ⟨Kw, hlev, -, hKGL, hcong⟩ := hC E l ι a ha hRk T hT U hU w₀ v' hw₀ hsp₀ hv' hspv hvap
  have hlsplit : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → IsSplitAt w := fun w hw =>
    Classical.byContradiction fun h => (hF.2.2.2 w h).1 hw
  have hfin := finite_not_sph a U hU.1
  set S : Finset (HeightOneSpectrum (𝓞 E)) := hfin.toFinset with hSdef
  have hsph : ∀ w, IsSplitAt w → ApartAll S w → ∃ B, SatU U w B := by
    intro w hs hA
    by_contra h
    exact hA w (hfin.mem_toFinset.2 ⟨hs, h⟩) rfl
  have hSap : ∀ w, IsSplitAt w → (∃ B, SatU U w B) → ApartAll S w := by
    intro w hs hB u hu hwu
    exact (hfin.mem_toFinset.1 hu).2 (GlobalTheory.CongL.SatConj.exists_satU_of_under_eq E a U hU.1 w u hs hwu.symm hB)
  set W0 : Set (HeightOneSpectrum (𝓞 E)) := {w | IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ ∃ B, SatU U w B} with hW0def
  have hW0 : ∀ w ∈ W0, IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ Kw w = GlobalTheory.LFun.KGL w (n := a) := fun w hw =>
    ⟨hw.1, hw.2.1, hKGL w hw.1 (apart_of_not_mem hw₀ hw.2.1) (apart_of_not_mem hv' hw.2.1) hw.2.2⟩
  obtain ⟨J, O, x, fr, n, hx, hpl, hcov, hrat, hidx, hconv⟩ := GlobalTheory.FrobOpsIdx.frobOpsIdx hS E Ω l ι a Kw W0 hW0
  have hcomp : ∀ U' : Submodule ℂ (UA E a → ℂ), IsAutRepU U' → ∀ w, IsSplitAt w →
      ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U' (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ :=
    fun U' hU' w hw => (GlobalTheory.SplitComp.exists_comp_and_unique E a U' hU' w hw).1
  obtain ⟨θ, hθ⟩ : ∃ θ : J → Qbar l, IsSysU O U θ := by
    choose σ hσ using fun j => hcomp U hU.1 (O.pl j) (O.split j)
    refine ⟨fun j => ι.symm (O.z j (σ j)), fun j σ' h' => ?_⟩
    obtain ⟨e⟩ := (GlobalTheory.SplitComp.exists_comp_and_unique E a U hU.1 (O.pl j) (O.split j)).2 _ _ (hσ j) h'
    show ι.symm (O.z j (σ j)) = ι.symm (O.z j σ')
    rw [z_eq_of_equiv O j e (hlev _ (O.split j) (apart_of_not_mem hw₀ (O.away j)) (apart_of_not_mem hv' (O.away j)) _ (hσ j))]
  have hsphSeed : ∀ U' : Submodule ℂ (UA E a → ℂ), IsAutRepU U' → HasLevelOff w₀ v' Kw U' → (∃ B, SatU U' v' B) →
      SphOffU w₀ S U' := by
    intro U' hU' hl' hb w hs hap hA
    by_cases hv : Apart w v'
    swap
    · exact GlobalTheory.CongL.SatConj.exists_satU_of_under_eq E a U' hU' v' w hspv (not_not.1 hv) hb
    obtain ⟨σ, hσ⟩ := hcomp U' hU' w hs
    have hfix := hl' w hs hap hv σ hσ
    rw [hKGL w hs hap hv (hsph w hs hA)] at hfix
    obtain ⟨B, hB⟩ := (hS E w a).1 σ hfix
    exact ⟨B, σ, hσ, hB⟩
  choose Z₀ hZ₀ hQ using fun Y => hSd E Ω l ι a ha hRk d hF T hT w₀ v' hw₀ hsp₀ hv' hspv hvap U S Y
  choose! rr hrr using hQ
  let Zs : Finset (HeightOneSpectrum (𝓞 E)) → Finset (HeightOneSpectrum (𝓞 E)) := fun Y =>
    Z₀ Y ∪ Y.filter (fun w => IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ ∃ B, SatU U w B)
  have hZs : ∀ Y, ∀ z ∈ Zs Y, IsSplitAt z ∧ Apart z w₀ ∧ Apart z v' ∧ ∃ B, SatU U z B := by
    intro Y z hz
    rcases Finset.mem_union.1 hz with h | h
    · obtain ⟨hus, hzl, hap, hA⟩ := hZ₀ Y z h
      exact ⟨hus.1, hap, apart_of_not_mem hv' hzl, hsph z hus.1 hA⟩
    · obtain ⟨-, hs, hzl, hB⟩ := Finset.mem_filter.1 h
      exact ⟨hs, apart_of_not_mem hw₀ hzl, apart_of_not_mem hv' hzl, hB⟩
  let Ws : Finset (HeightOneSpectrum (𝓞 E)) → Finset (HeightOneSpectrum (𝓞 E)) := fun Y =>
    Y.filter (fun w => ((l : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ Apart w w₀ ∧ Apart w v' ∧ ∃ B, SatU U w B)
  choose cc hcc0 hcc using fun Y => hcong (Zs Y) (Ws Y) (hZs Y) fun w hw =>
    ⟨hlsplit w (Finset.mem_filter.1 hw).2.1, (Finset.mem_filter.1 hw).2⟩
  let Good : Finset (HeightOneSpectrum (𝓞 E)) → Submodule ℂ (UA E a → ℂ) → (J → Qbar l) → Prop := fun Y U' θ' =>
    AutOffT T U' ∧ HasLevelOff w₀ v' Kw U' ∧ ((∃ B, SatU U' v' B) ∧ SameWtOff ι w₀ v' U U' ∧ ∀ w ∈ Ws Y, GenAtU Gen U' w) ∧
      Wt E l a ι w₀ v' U U' ∧ Ty E l a w₀ U' ∧ (∀ z ∈ Zs Y, GenAtU Gen U' z) ∧ IsSysU O U' θ'
  let I : Type := {p : Finset (HeightOneSpectrum (𝓞 E)) × Submodule ℂ (UA E a → ℂ) × (J → Qbar l) // Good p.1 p.2.1 p.2.2}
  let ρ : I → (Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) := fun i => rr i.1.1 i.1.2.1
  let η : I → J → Qbar l := fun i => i.1.2.2
  let D : I → Set J := fun i => {j | η i j = trc (ρ i) (x j)}
  have hQi := fun i : I => hrr i.1.1 i.1.2.1 i.2.1 i.2.2.2.2.2.1 i.2.2.2.2.1 (hsphSeed _ i.2.1.1 i.2.2.1 i.2.2.2.1.1) i.2.2.2.1.1
    (fun z hz => i.2.2.2.2.2.2.1 z (Finset.mem_union_left _ hz))
  have hpaJ : ∀ Y, PolyApprox (Sum.elim θ fun p : ↥(Ws Y) × ℤ => ι.symm (cc Y p.1 p.2 * PowSatU U p.1 p.2))
      ((fun i : I => Sum.elim (η i) fun p : ↥(Ws Y) × ℤ => ι.symm (cc Y p.1 p.2 * PowSatU i.1.2.1 p.1 p.2)) ''
        {i : I | i.1.1 = Y}) := by
    intro Y
    refine ((hcc Y J O θ hθ).1).mono ?_
    rintro _ ⟨U', θ', h1, h2, hb, h3, h4, h5, h6, hW, h7, rfl⟩
    exact ⟨⟨(Y, U', θ'), h1, h2, ⟨hb, h3, hW⟩, h4, h5, h6, h7⟩, rfl, rfl⟩
  have hpaY : ∀ Y, PolyApprox θ (η '' {i : I | i.1.1 = Y}) := fun Y => approx_left (hpaJ Y)
  obtain ⟨L, hL⟩ := (hcc ∅ J O θ hθ).2 hrat
  have hdense : ∀ s : Finset I, Dense (x '' ⋂ i ∈ s, D i) := by
    intro s
    choose V X hVo hVd hVX using fun i : I => (hQi i).2.2.1
    have hVa : ∀ t : Finset I, IsOpen (⋂ i ∈ t, V i) ∧ Dense (⋂ i ∈ t, V i) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp
      | insert b t hb ih =>
        rw [Finset.set_biInter_insert]
        exact ⟨(hVo b).inter ih.1, (hVd b).inter_of_isOpen_left ih.2 (hVo b)⟩
    have hD := (dense_frob_usable_off E Ω l hl d hF.1 (S ∪ s.biUnion X)).inter_of_isOpen_right (hVa s).2 (hVa s).1
    refine Dense.mono ?_ ((inv_surjective.denseRange).dense_image continuous_inv hD)
    rintro _ ⟨g, ⟨⟨w, hwX, hus, hwl, hA, A, hAw, hg⟩, hgV⟩, rfl⟩
    have hwS : ApartAll S w := fun u hu => hA u (Finset.mem_union_left _ hu)
    have hsw : ∃ B, SatU U w B := hsph w hus.1 hwS
    obtain ⟨j, hj1, hj2, hj3⟩ := hcov w ⟨hus.1, hwl, hsw⟩ A hAw g hg
    refine ⟨j, ?_, by rw [hx j, hj2, hj3, pow_one]⟩
    simp only [Set.mem_iInter]
    intro i hi
    subst hj1
    have hap := apart_of_not_mem hw₀ hwl
    obtain ⟨B', σ', hσ', hB'⟩ := hsphSeed _ i.2.1.1 i.2.2.1 i.2.2.2.1.1 (O.pl j) hus.1 hap hwS
    have hchar := ((hVX i (O.pl j) (fun h => hwX (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, h⟩)))
      hus hwl hwS B' ⟨σ', hσ', hB'⟩ A hAw).2 g hg (Set.mem_iInter₂.1 hgV i hi))
    show i.1.2.2 j = trc (ρ i) (x j)
    rw [i.2.2.2.2.2.2.2 j σ' hσ']
    exact hidx j σ' (i.2.2.1 (O.pl j) hus.1 hap (apart_of_not_mem hv' hwl) σ' hσ') B' hB' (ρ i) (by rw [hj2]; exact hchar)
  obtain ⟨t, htL, ht3, ht⟩ := exists_trace_limit l (Formalism.ConjugateSelfDual.G E Ω) a J I x θ L.1 L.2 hL ρ η D
    (fun i => (hQi i).1) (fun i j hj => hj) hdense ((hpaY ∅).mono (Set.image_subset_range _ _))
  have hpt : PolyApprox t ((fun ρ' g => trc ρ' (id g)) '' Set.range ρ) := by
    have := (ht Set.univ (by rw [Set.image_univ]; exact (hpaY ∅).mono (Set.image_subset_range _ _))).1
    rw [Set.image_univ] at this
    rw [← Set.range_comp]
    exact this
  obtain ⟨r, hrc, hrss, hrt, -⟩ := GlobalTheory.Cong.exists_limit_rep l (Formalism.ConjugateSelfDual.G E Ω) a (Formalism.ConjugateSelfDual.G E Ω) id denseRange_id t L.1 L.2 htL
    (Set.range ρ) (by rintro _ ⟨i, rfl⟩; exact (hQi i).1) hpt
  have htr : trc r = t := funext hrt
  have hlin : ∀ A : Set I, PolyApprox θ (η '' A) → LinApprox r (ρ '' A) := by
    intro A hA
    refine GlobalTheory.Cong.linApprox_of_polyApprox_trc (Qbar l) (Formalism.ConjugateSelfDual.G E Ω) a r (ρ '' A) ?_
    rw [htr, Set.image_image]
    exact (ht A hA).1
  refine ⟨r, hrc, hrss, ?_, ?_, ?_⟩
  · intro w hwU hwl B hB
    have hws := hwU.1
    have hsw : ∃ B, SatU U w B := ⟨B, hB⟩
    have hwS := hSap w hws hsw
    have hap := apart_of_not_mem hw₀ hwl
    have hwZ : ∀ i : I, i.1.1 = {w} → w ∈ Zs i.1.1 := fun i hi => by
      rw [hi]
      exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_singleton_self w, hws, hwl, hsw⟩)
    have hseedFE : ∀ i : I, i.1.1 = {w} → ∀ B', SatU i.1.2.1 w B' →
        UpperTheory.V.Af.FrobEig ι (ρ i) w (UpperTheory.V.Af.algSat a (normV w) B') := by
      intro i hi B' hB'
      have hwY : w ∈ i.1.1 := by rw [hi]; exact Finset.mem_singleton_self w
      exact (hQi i).2.2.2.1 w hwY hwU hwl hwS B' hB' (i.2.2.2.2.2.2.1 w (hwZ i hi) B' hB')
    have hlin0 := hlin {i : I | i.1.1 = {w}} (hpaY {w})
    intro A hA
    refine ⟨fun s hs => GlobalTheory.Cong.ker_of_linApprox l (Formalism.ConjugateSelfDual.G E Ω) a r _ hrss hlin0 s ?_, fun s hs => ?_⟩
    · rintro _ ⟨i, hi, rfl⟩
      obtain ⟨B', hB'⟩ := hsphSeed _ i.2.1.1 i.2.2.1 i.2.2.2.1.1 w hws hap hwS
      exact (hseedFE i hi B' hB' A hA).1 s hs
    · obtain ⟨σ, hσ, hBσ⟩ := hB
      refine hconv w ⟨hws, hwl, hsw⟩ σ (hlev w hws hap (apart_of_not_mem hv' hwl) σ hσ) B hBσ r ?_ A hA s hs
      intro j hj
      subst hj
      rw [htr, (ht {i : I | i.1.1 = {O.pl j}} (hpaY {O.pl j})).2 j ?_]
      · exact hθ j σ hσ
      · intro i hi
        obtain ⟨B', σ', hσ', hB'⟩ := hsphSeed _ i.2.1.1 i.2.2.1 i.2.2.2.1.1 (O.pl j) hws hap hwS
        obtain ⟨A', hA', hfr⟩ := (hpl j).2
        have hFE := (hseedFE i hi B' ⟨σ', hσ', hB'⟩ A' hA').2 (fr j) hfr
        show i.1.2.2 j = trc (ρ i) (x j)
        rw [i.2.2.2.2.2.2.2 j σ' hσ']
        exact hidx j σ' (i.2.2.1 (O.pl j) hws hap (apart_of_not_mem hv' hwl) σ' hσ') B' hB' (ρ i) hFE
  · intro w hwl hap hapv hsw
    refine GlobalTheory.CongL.crysDRU_of_linApprox GlobalTheory.LimitTop.closedAtL E Ω l ι a ha U hU.1
      (GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU E a ha U hU.1) r w hwl hrc hrss _ (hlin _ (hpaY {w})) ?_
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨(hQi i).1, i.1.2.1, sameWtAt_of_off ι i.2.2.2.1.2.1 (fun τ hτ u hu => overPl_unique ι τ hτ hu) hap hapv,
      (hQi i).2.2.2.2.1 w (by rw [show i.1.1 = {w} from hi]; exact Finset.mem_singleton_self w) hwl hap hapv
        (hSap w (hlsplit w hwl) hsw)⟩
  · intro w hwl hap hapv B hB P AI hTi A hA O' _ _ _ Bw hBw σ
    have hws := hlsplit w hwl
    have hwS := hSap w hws ⟨B, hB⟩
    have hwW : w ∈ Ws {w} := Finset.mem_filter.2 ⟨Finset.mem_singleton_self w, hwl, hap, hapv, B, hB⟩
    have hwY : ∀ i : I, i.1.1 = {w} → w ∈ i.1.1 := fun i hi => by rw [hi]; exact Finset.mem_singleton_self w
    choose lam hlam using GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU E a ha U hU.1
    refine ⟨ρ '' {i : I | i.1.1 = {w}}, fun τ => LimAtLU.jumpsOf (lam (ι.toRingHom.comp τ)), ?_, ?_⟩
    · rintro _ ⟨i, hi, rfl⟩
      have h := (hQi i).2.2.2.2.1 w (hwY i hi) hwl hap hapv hwS P AI hTi A hA O' Bw hBw
      have hWW := sameWtAt_of_off ι i.2.2.2.1.2.1 (fun τ hτ u hu => overPl_unique ι τ hτ hu) hap hapv
      exact ⟨(hQi i).1, h.1, fun τ LL' τ' hi' => h.2.2 τ LL' τ' hi' _ _
        ((hWW _ (LimAtLU.overPl_of_induced ι hA hBw hi') _).1 (hlam _)) (LimAtLU.jumpsOf_map _)⟩
    · have hu : ∀ (n : ℤ) (z : ℂ), ι.symm z = (ι.symm (cc {w} w n))⁻¹ * ι.symm (cc {w} w n * z) := fun n z => by
        rw [map_mul, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero ι.symm).2 (hcc0 {w} w n)), one_mul]
      refine joint (hpaJ {w}) (fun F c ε hP g => by rw [htr]; exact ht3 F c ε hP g) _ _
        (fun n => (⟨w, hwW⟩, -(deg σ) * n)) (fun n => (ι.symm (cc {w} w (-(deg σ) * n)))⁻¹) (fun n => ?_) (fun i hi n => ?_)
      · rw [phiSum_satWD, ← powSatU_eq hU.1 hws hB]
        exact hu _ _
      · obtain ⟨B', hB'⟩ := hsphSeed _ i.2.1.1 i.2.2.1 i.2.2.2.1.1 w hws hap hwS
        have hg : Gen a (normV w) B' := i.2.2.2.1.2.2 w (by rw [show i.1.1 = {w} from hi]; exact hwW) B' hB'
        have e := (hQi i).2.2.2.2.2 w (hwY i hi) hwl hap hapv hwS B' hB' hg P AI hTi A hA O' Bw hBw σ n
        rw [phiSum_satWD, ← powSatU_eq i.2.1.1 hws hB'] at e
        exact (congrArg ι.symm e).trans (hu _ _)

theorem limFinOdd_of (h : SeedFinOdd) (h' : CongFinOdd) : LimFinOdd := limWU4_of _ _ _ _ h h'

end UpperTheory.Gal.Lim
end
end
