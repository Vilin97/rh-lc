module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.ArPl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArPres
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.UnrLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DOSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArPresAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.GwCntBare
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.LocCntBare
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.UnrDev
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.ResidualRepOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.PsiInj
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.LocCntCongr

section

@[expose] public section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.locCntCongr :
    ∀ (l : ℕ) [Fact l.Prime] (D D' : Type) [Group D] [TopologicalSpace D] [Group D'] [TopologicalSpace D'] (α : D ≃ₜ* D') (ε : D →* ℤ_[l]ˣ) (ε' : D' →* ℤ_[l]ˣ) (d : ℕ), (∀ g, ε g = ε' (α g)) → LocCnt D' ε' d → LocCnt D ε d := by
  intro l _ D D' _ _ _ _ α ε ε' d hε H k hk R M M' _ _ _ _ _ _ _ ρ ρ' b hLC hb
  let β : D' →* D := α.symm.toMulEquiv.toMonoidHom
  let σ : Representation R D' M := ρ.comp β
  let σ' : Representation R D' M' := ρ'.comp β
  have hσ : ∀ g, σ g = ρ (α.symm g) := fun _ => rfl
  have hσ' : ∀ g, σ' g = ρ' (α.symm g) := fun _ => rfl
  have h1 : LC σ := fun m => (hLC m).comp_continuous α.symm.continuous
  have h2 : DualPair k ε' σ σ' b := by
    refine ⟨hb.left, hb.right, fun g x y => ?_⟩
    rw [hσ, hσ', hb.equiv]
    simp only [hε, ContinuousMulEquiv.apply_symm_apply]
  obtain ⟨hf, hc⟩ := H k hk R M M' σ σ' b h1 h2
  let e : Zl ρ ≃ Zl σ :=
    { toFun := fun z => ⟨fun g => z.1 (α.symm g), z.2.1.comp_continuous α.symm.continuous, fun g h => by
        beta_reduce
        rw [map_mul, z.2.2, hσ]⟩
      invFun := fun z => ⟨fun g => z.1 (α g), z.2.1.comp_continuous α.continuous, fun g h => by
        beta_reduce
        rw [map_mul, z.2.2, hσ, ContinuousMulEquiv.symm_apply_apply]⟩
      left_inv := fun z => Subtype.ext (funext fun g => by simp)
      right_inv := fun z => Subtype.ext (funext fun g => by simp) }
  have hi : ρ'.invariants = σ'.invariants := by
    ext m
    simp only [Representation.mem_invariants, hσ']
    exact ⟨fun h g => h _, fun h g => by simpa using h (α g)⟩
  exact ⟨Finite.of_equiv _ e.symm, by rw [Nat.card_congr e, hc, hi]⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PresCnts

section

@[expose] public section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.presCnts :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (Lc : Loc) (G : Glob l Lc) (q d : ℕ) (a : ArData G q d) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (_ : ArPres a F Ω), l ≠ 2 → (∀ u, UnrCount l (Lc.Gu u) (Lc.Ju u)) → Cnts a := by
  intro hC l _ Lc G q d a F Ω _ _ _ _ _ _ P hl hU
  have hmatch : ∀ (w : ArData.W Lc q) (g : a.D w),
      G.ε (a.ι w g) = cycZ F Ω l ((Dec (P.A w)).subtype (P.α w g)) := by
    intro w g
    exact (congrArg G.ε (P.ι_eq w g)).trans (P.e_ε _)
  refine Cnts.mk ?_ ?_ ?_ ?_
  · have key := gwCntBare hC.gw hC.lt hC.gf hC.lf l F Ω P.S G.Γ P.e G.ε (ArData.W Lc q) P.pl P.A
      a.D a.ι P.α d P.ip P.c hl P.above P.e_ε P.isOver P.ι_eq P.cc
    have hcw : a.cw = fun i => P.e ((toGS Ω P.S) (P.c i)) := funext P.cw_eq
    rw [hcw]
    exact key
  · intro v
    have hv : (l : 𝓞 F) ∈ (P.pl (Sum.inl v) : HeightOneSpectrum (𝓞 F)).asIdeal := (P.pl_l _).2 ⟨v, rfl⟩
    have h1 := (locCntBare hC.lf hC.lt hC.le l F Ω (P.A (Sum.inl v)) _ (P.isOver (Sum.inl v))).1 hv
    rw [P.dv_eq v]
    exact locCntCongr l (a.D (Sum.inl v)) _ (P.α (Sum.inl v)) _ _ _ (hmatch (Sum.inl v)) h1
  · intro j
    have hn : (l : 𝓞 F) ∉ (P.pl (Sum.inr (Sum.inr j)) : HeightOneSpectrum (𝓞 F)).asIdeal := by
      intro hm
      obtain ⟨v, hv⟩ := (P.pl_l _).1 hm
      cases hv
    have h0 := (locCntBare hC.lf hC.lt hC.le l F Ω (P.A (Sum.inr (Sum.inr j))) _
      (P.isOver (Sum.inr (Sum.inr j)))).2 hn
    exact locCntCongr l (a.D (Sum.inr (Sum.inr j))) _ (P.α (Sum.inr (Sum.inr j))) _ _ _
      (hmatch (Sum.inr (Sum.inr j))) h0
  · intro u
    exact unrDev l _ _ (hU u)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.OrdinaryHeckeAlgebraIntegral

section

@[expose] public section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : Coef l) : IsCoef l c.O := by
  obtain ⟨h1, h2, h3, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨h1, h2, ?_⟩
  rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff]
  exact h3

private theorem eps_ne {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A w) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) :
    ∃ g : Dec (F := L) A, cycZ L Ω l g ≠ 1 := by
  by_contra hn
  have hn' : ∀ g : Dec (F := L) A, cycBar L Ω l g = 1 := fun g => by
    have : cycZ L Ω l g = 1 := by
      by_contra h1
      exact hn ⟨g, h1⟩
    rw [cycBar, MonoidHom.comp_apply, this, map_one]
  have := UpperTheory.V.Ws.Eb.psiInj (l := l) A w h hw (n := 2) (fun _ => 1) ![0, 1] 1 (by decide) one_pos
    (fun i g _ => by rw [hn' g]; simp)
  exact absurd (@this 0 1 rfl) (by decide)

theorem UpperTheory.V.Th.b1O : ordinaryHeckeAlgebraIntegral := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 c n r T P y al hS _ _ hPL h4 heig hdet
  haveI := coef_isCoef l c
  choose a p h1 h2 h3 using arPres l L Ω s V0 c.O n r T P hS
  have S : Sys T (Module.finrank ℚ (Lp L)) V0.frame.D0 :=
    { a := a
      counts := fun N => presCnts hP l _ _ _ _ (a N) (Lp L) Ω (p N) s.odd (unrLoc l L Ω s V0 c.O n r)
      dv := fun v : Vl l L => locDeg v.1
      dv_eq := fun N => funext (h1 N)
      d0 := h2
      ph := fun N j => (h3 N j).1
      ta := fun N j => (h3 N j).2 }
  have hΦ := (arPl hP l L Ω s V0 c.O n r hS).1
  refine b1absO l _ _ T c.O n y al _ _ S s.odd hΦ (fun v => ?_) hPL h4 heig (detO l _ _ c n y _ s.odd hdet)
  have hw : ((l : ℕ) : 𝓞 L) ∈ (s.w v.1).asIdeal := by
    have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (Lp L))).2 v.2
    exact (s.hw v.1 _).1 (by simpa using h1)
  obtain ⟨g, hg⟩ := eps_ne (s.A v.1) (s.w v.1) (s.hw v.1) hw
  refine ⟨g, fun e => hg (Units.ext ?_)⟩
  have e1 : V0.ε (toGS Ω V0.S' (resP L Ω g)) = cycZ (Lp L) Ω l (resP L Ω g) := DFunLike.congr_fun V0.hε _
  have e2 : algebraMap ℤ_[l] c.O (V0.ε (toGS Ω V0.S' (resP L Ω g)) : ℤ_[l]) = 1 := e
  rw [e1, ← map_one (algebraMap ℤ_[l] c.O)] at e2
  exact (UpperTheory.V.abelian₂.dvr_finite l c.O).2.2.2.1 e2
end
end
