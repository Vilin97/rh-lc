module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PNoLogSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteLeOfClosureClasses
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteOfCapelliMonic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermCofiniteIdealTransfer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmaller
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceA
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceF
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceA
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceD
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceE
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceF

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.ExpChar

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUB2

def expChar (c : ℂ) : Multiplicative ℝ →* ℂ where
  toFun t := Complex.exp (c * ((Multiplicative.toAdd t : ℝ) : ℂ))
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem lagrange (C : Finset ℂ) (c : ℂ) : ∃ (τs : Finset ℝ) (a : ℝ → ℂ), ∀ c' ∈ C,
    ∑ t ∈ τs, a t * Complex.exp (c' * t) = if c' = c then 1 else 0 := by
  classical
  have expChar_injective : Function.Injective expChar := by
    intro c c' h
    have hd : ∀ d : ℂ, HasDerivAt (fun t : ℝ => Complex.exp (d * (t : ℂ))) d 0 := by
      intro d
      have h1 : HasDerivAt (fun t : ℝ => d * (t : ℂ)) (d * 1) 0 :=
        ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul d
      have h2 := h1.cexp
      simpa using h2
    have hf : (fun t : ℝ => Complex.exp (c * (t : ℂ))) = fun t : ℝ => Complex.exp (c' * (t : ℂ)) := by
      funext t
      have := DFunLike.congr_fun h (Multiplicative.ofAdd t)
      simpa [expChar] using this
    have e := hd c
    rw [hf] at e
    exact e.unique (hd c')
  let v : ℝ → (C → ℂ) := fun t c' => Complex.exp ((c' : ℂ) * t)
  have hli : LinearIndependent ℂ (fun c' : C => (expChar (c' : ℂ) : Multiplicative ℝ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp (fun c' : C => expChar (c' : ℂ))
      (expChar_injective.comp Subtype.val_injective)
  have htop : Submodule.span ℂ (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have hw : ∀ i : C, f (Pi.single i 1) = 0 := by
      have hsum : ∑ i : C, f (Pi.single i 1) • (expChar (i : ℂ) : Multiplicative ℝ → ℂ) = 0 := by
        funext x
        have hx : f (v (Multiplicative.toAdd x)) = 0 := hle (Submodule.subset_span ⟨_, rfl⟩)
        have hv : v (Multiplicative.toAdd x) = ∑ i : C, (v (Multiplicative.toAdd x) i) • Pi.single i 1 := by
          funext j
          simp [Finset.sum_apply, Pi.single_apply]

        rw [hv, map_sum] at hx
        simp only [map_smul, smul_eq_mul] at hx
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← hx]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [expChar, v, mul_comm]
      exact fun i => Fintype.linearIndependent_iff.1 hli _ hsum i
    exact (Pi.basisFun ℂ C).ext fun i => by simpa using hw i
  have hmem : (fun c' : C => if (c' : ℂ) = c then (1 : ℂ) else 0) ∈ Submodule.span ℂ (Set.range v) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  refine ⟨a.support, a, fun c' hc' => ?_⟩
  have := congrFun ha ⟨c', hc'⟩
  rw [Finsupp.sum, Finset.sum_apply] at this
  simpa [v] using this

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUB2

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PSliceUA

section

@[expose] public section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl PositivityTheory.Rg.Rs
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm PositivityTheory.Rg.Rs.SliceClasses

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.LieSumUnipotentSlice

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem F_slicesU (V : Submodule ℂ (Sm E (r + s))) (hVs : _root_.GlobalTheory.CuspRep.IsStable V) (hVa : ∀ φ ∈ V, IsAutForm φ)
    (hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ c : ℂ, ∀ ψ ∈ V, cap τ u ψ = c • ψ) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s))
    (hequiv : ∀ o, ∀ φ ∈ V, T (act o φ) = act o (T φ)) (τs : Finset ℝ) (a : ℝ → ℂ)
    (hTval : ∀ φ ∈ V, ∀ g, (T φ).1 g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g))
    (φ : Sm E (r + s)) (hφ : φ ∈ V) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    (∀ m₂, ∃ ψ : Sm E r, IsAutForm ψ ∧ ∀ m₁, ψ.1 m₁ =
      (T φ).1 (lev (Ad E) r s (m₁, m₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) ∧
    (∀ m₁, ∃ ψ : Sm E s, IsAutForm ψ ∧ ∀ m₂, ψ.1 m₂ =
      (T φ).1 (lev (Ad E) r s (m₁, m₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) := by
  have hAφ := hVa φ hφ

  have hN : ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), (T φ).1 (unip x * g) = (T φ).1 g := by
    intro x g
    rw [hTval φ hφ, hTval φ hφ]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨y, hy⟩ := aT_mul_unip (r + s) r t x
    rw [← mul_assoc, hy, mul_assoc, ctn_unip hAφ]

  have hM : ∀ (γ : GL (Fin r) E × GL (Fin s) E) (g : GA E (r + s)),
      (T φ).1 (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g) = (T φ).1 g := by
    intro γ g
    rw [hTval φ hφ, hTval φ hφ]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← mul_assoc, aT_comm_lev, mul_assoc, ctn_lev_rat hAφ]

  let L := GlobalTheory.DiscClosure.stabSub φ
  have hLo : IsOpen (L : Set (GL (Fin (r + s)) (Af E))) := hAφ.level
  have hLv : ∀ h ∈ L, finRep E (r + s) h (T φ) = T φ := fun h hh => by
    have e := hequiv (.fin h) φ hφ
    have hh' : finRep E (r + s) h φ = φ := hh
    change T (finRep E (r + s) h φ) = finRep E (r + s) h (T φ) at e
    rw [← e, hh']

  let S := GlobalTheory.CuspRep.LocEx.orbSpan (T φ)
  haveI : FiniteDimensional ℂ S := by
    haveI := hAφ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun κ => cptRep E (r + s) κ φ)).map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨κ, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨κ, rfl⟩, hequiv (.cpt κ) φ hφ⟩
  let ρ := GlobalTheory.PRep.sub (cptRep E (r + s)) S (GlobalTheory.CuspRep.LocEx.orbSpan_stable (T φ))
  have hρ : GlobalTheory.Published.AutFin.IsContRep ρ := GlobalTheory.CuspRep.LocEx.isContRep_sub S _
  have hC : ∀ g : GA E (r + s), (fun κ : Kinf E (r + s) => (cptRep E (r + s) κ (T φ)).1 g) ∈
      GlobalTheory.Published.AutFin.coeffSpan ρ := fun g =>
    GlobalTheory.Published.AutFinGL.type_of_map ρ S.subtype (fun _ _ => rfl) ⟨T φ, Submodule.subset_span ⟨1, by simp⟩⟩ g

  have hG : ∀ g₀ : GA E (r + s), ∃ (C : ℝ) (n : ℕ), ∀ y, ‖(T φ).1 (g₀ * infGL E (r + s) y)‖ ≤ C * height y ^ n := by
    intro g₀
    choose C n hCn using fun t => ctn_growth hAφ r (aT E (r + s) r t * g₀)
    refine ⟨∑ t ∈ τs, ‖a t‖ * |C t|, ∑ t ∈ τs, n t, fun y => ?_⟩
    rw [hTval φ hφ, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => ?_)
    have hy := one_le_height y
    have e1 : height y ^ n t ≤ height y ^ (∑ t ∈ τs, n t) :=
      pow_le_pow_right₀ hy (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ht)
    have hp : (0 : ℝ) ≤ height y ^ n t := pow_nonneg (by linarith) _
    calc ‖a t * An.ctn r φ.1 (aT E (r + s) r t * (g₀ * infGL E (r + s) y))‖
        = ‖a t‖ * ‖An.ctn r φ.1 (aT E (r + s) r t * g₀ * infGL E (r + s) y)‖ := by rw [norm_mul, mul_assoc]
      _ ≤ ‖a t‖ * (C t * height y ^ n t) := mul_le_mul_of_nonneg_left (hCn t y) (norm_nonneg _)
      _ ≤ ‖a t‖ * (|C t| * height y ^ (∑ t ∈ τs, n t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (le_abs_self _) e1 hp (abs_nonneg _)) (norm_nonneg _)
      _ = ‖a t‖ * |C t| * height y ^ (∑ t ∈ τs, n t) := by ring

  choose cc hcc using hsc
  let J : Set (Module.End ℂ (Sm E (r + s))) :=
    {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = Polynomial.aeval (cap (a := r + s) τ u) (Polynomial.X - Polynomial.C (cc τ u))}
  have hJZ : J ⊆ Zalg E (r + s) := by
    rintro _ ⟨τ, u, rfl⟩
    exact aeval_mem_Zalg (cap_mem_Zalg τ u) _
  have hJ : Cofin J := GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic E (r + s) J hJZ fun τ u =>
    ⟨_, Polynomial.monic_X_sub_C _, τ, u, rfl⟩
  have hZ : ∀ z ∈ J, z (T φ) = 0 := by
    rintro _ ⟨τ, u, rfl⟩
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply]
    rw [← GlobalTheory.SpehInfChar.cap_comm_quot (fun X ψ hψ => hVs (.lie X) ψ hψ) T hequiv τ u φ hφ,
      hcc τ u φ hφ, map_smul, sub_self]
  have hgood : T φ ∈ goodCT L ρ J := ⟨hN, hM, hLv, hC, hG, hZ⟩
  obtain ⟨J₁, J₂, c₁, c₂, k₁, k₂⟩ := centre J hJ
  have e : ∀ m : GA E r × GA E s, lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g) =
      lev (Ad E) r s m * finGL E (r + s) g * infGL E (r + s) (Unitary.toUnits k) := by
    intro m
    rw [infGL_comm, mul_assoc]
  refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
  · obtain ⟨L₁, ρ₁, -, -, h⟩ := Slice1.slice_mem_genSpace E r s L hLo S ρ hρ J hJ J₁ c₁ k₁ g k
    obtain ⟨G, hG, hG'⟩ := h (T φ) hgood m₂
    exact ⟨G, hG.1, fun m₁ => by rw [hG', e]⟩
  · obtain ⟨L₂, ρ₂, -, -, h⟩ := Slice2.slice2 E r s L hLo S ρ hρ J hJ J₂ c₂ k₂ g k
    obtain ⟨G, hG, hG'⟩ := h (T φ) hgood m₁
    exact ⟨G, hG.1, fun m₂ => by rw [hG', e]⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.LieSumUnipotentSlice

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SliceUOfNoLog2

section

@[expose] public section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUniqueness


open LieSumUnipotentSlice PositivityTheory.Rg.Rs.SliceClasses in
theorem sliceU_of_noLog2 (hNL : NoLog) : SliceU := by
  intro E _ _ _ r s hr hs U hU hFG hSI hReg φ hφU c hc
  have hD := dict_holds
  have hFin := finTr_holds
  obtain ⟨F₀, hCT, F, hFspan, hFne, hFeig⟩ := hc
  have hAφ := hU.2 φ hφU
  obtain ⟨κ, -, rfl⟩ := ((hD E (r + s)).2.2.2 φ hAφ r hr (by omega)).2 F₀ hCT
  obtain ⟨cs, hcs⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hFspan
  obtain ⟨b, hb⟩ : ∃ b : ℝ → ℂ, b = fun t => cs t * κ := ⟨_, rfl⟩
  have hFval : ∀ g, F g = ∑ t ∈ cs.support, b t * An.ctn r φ.1 (aT E (r + s) r t * g) := by
    intro g
    rw [← hcs, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, hb, mul_assoc]

  obtain ⟨S, hSU, hSgen⟩ := hFG
  have hregψ : ∀ ψ ∈ U, ∀ τ : E →+* ℂ, ∃ m, HasInfCharGL (Submodule.span ℂ {ψ}) τ m ∧ m.Nodup := by
    intro ψ hψ τ
    obtain ⟨m, ⟨hcard, hm⟩, hnd⟩ := hReg τ
    exact ⟨m, ⟨hcard, fun u χ hχ => hm u χ ((Submodule.span_singleton_le_iff_mem ψ U).2 hψ hχ)⟩, hnd⟩
  have hdec : ∀ ψ ∈ S, ∃ (C : Finset ℂ) (G : ℂ → GA E (r + s) → ℂ), An.ctn r ψ.1 = ∑ c ∈ C, G c ∧
      ∀ c ∈ C, ∀ (t : ℝ) g, G c (aT E (r + s) r t * g) = Complex.exp (c * t) * G c g := fun ψ hψ =>
    hNL E (r + s) r ψ (hU.2 ψ (hSU hψ)) (hSI ψ (hSU hψ)) (hregψ ψ (hSU hψ)) hr (by omega)
  choose! Cs Gs hsum hGeig using hdec
  obtain ⟨τs, a, ha⟩ := SliceUB2.lagrange (insert c (S.biUnion Cs)) c
  have ha1 : ∑ t ∈ τs, a t * Complex.exp (c * t) = 1 := by
    rw [ha c (Finset.mem_insert_self _ _), if_pos rfl]

  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring U hU.2 r τs a
  have hTval : ∀ ψ ∈ U, ∀ g, (T ψ).1 g = ∑ t ∈ τs, a t * An.ctn r ψ.1 (aT E (r + s) r t * g) := by
    intro ψ hψ g
    rw [hT ψ hψ, Aop_apply, ctSm_val r (hU.2 ψ hψ)]
  have hequiv : ∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ) := by
    intro o ψ hψ
    rw [hT _ (hU.1 o ψ hψ), hT ψ hψ, ctSm_act r (hU.2 ψ hψ) o (hU.2 _ (hU.1 o ψ hψ)), Aop_act]

  have hgen : ∀ ψ ∈ S, ∀ g, (T ψ).1 g = ∑ c' ∈ Cs ψ, (if c' = c then 1 else 0) * Gs ψ c' g := by
    intro ψ hψ g
    rw [hTval ψ (hSU hψ), hsum ψ hψ]
    calc ∑ t ∈ τs, a t * (∑ c' ∈ Cs ψ, Gs ψ c') (aT E (r + s) r t * g)
        = ∑ t ∈ τs, ∑ c' ∈ Cs ψ, a t * (Complex.exp (c' * t) * Gs ψ c' g) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c' hc' => by rw [hGeig ψ hψ c' hc']
      _ = ∑ c' ∈ Cs ψ, (∑ t ∈ τs, a t * Complex.exp (c' * t)) * Gs ψ c' g := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c' _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun t _ => by ring
      _ = ∑ c' ∈ Cs ψ, (if c' = c then 1 else 0) * Gs ψ c' g := by
          refine Finset.sum_congr rfl fun c' hc' => ?_
          rw [ha c' (Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨ψ, hψ, hc'⟩))]

  let W : Submodule ℂ (Sm E (r + s)) :=
    { carrier := {ψ | ψ ∈ U ∧ ∀ (t : ℝ) g, (T ψ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T ψ).1 g}
      add_mem' := fun {φ ψ} hφ hψ => ⟨U.add_mem hφ.1 hψ.1, fun t g => by
        simp only [map_add (f := _), Submodule.coe_add, Pi.add_apply, hφ.2 t g, hψ.2 t g, mul_add]⟩
      zero_mem' := ⟨U.zero_mem, fun t g => by simp⟩
      smul_mem' := fun b φ hφ => ⟨U.smul_mem b hφ.1, fun t g => by
        simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hφ.2 t g]
        ring⟩ }
  have hWst : _root_.GlobalTheory.CuspRep.IsStable W := by
    rintro o ψ ⟨hψ, he⟩
    refine ⟨hU.1 o ψ hψ, fun t g => ?_⟩
    have e1 : ltS (aT E (r + s) r t) (T ψ) = Complex.exp (c * t) • T ψ := Subtype.ext (funext fun g => he t g)
    have e2 := congrArg (fun G : Sm E (r + s) => G.1 g) (congrArg (act o) e1)
    simp only [← ltS_act, map_smul] at e2
    rw [hequiv o ψ hψ]
    exact e2
  have hSW : (↑S : Set (Sm E (r + s))) ⊆ W := by
    intro ψ hψ
    refine ⟨hSU hψ, fun t g => ?_⟩
    rw [hgen ψ hψ, hgen ψ hψ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' hc' => ?_
    rw [hGeig ψ hψ c' hc']
    split_ifs with h
    · subst h
      ring
    · simp
  have hUW : U ≤ W := hSgen W hWst hSW
  have heig : ∀ ψ ∈ U, ∀ (t : ℝ) g, (T ψ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T ψ).1 g :=
    fun ψ hψ => (hUW hψ).2

  have hTφ : T φ ≠ 0 := by
    intro h0
    have hz : ∀ g, ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g) = 0 := by
      intro g
      rw [← hTval φ hφU g, h0]
      rfl
    apply hFne
    funext g
    have hcomm : ∀ t t' : ℝ, aT E (r + s) r t' * (aT E (r + s) r t * g) =
        aT E (r + s) r t * (aT E (r + s) r t' * g) := by
      intro t t'
      rw [← mul_assoc, ← mul_assoc, ← aT_add, ← aT_add, add_comm t' t]
    calc F g = (∑ t' ∈ τs, a t' * Complex.exp (c * t')) * F g := by rw [ha1, one_mul]
      _ = ∑ t' ∈ τs, a t' * F (aT E (r + s) r t' * g) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun t' _ => by rw [hFeig t' g]; ring
      _ = ∑ t ∈ cs.support, b t * ∑ t' ∈ τs, a t' * An.ctn r φ.1 (aT E (r + s) r t' * (aT E (r + s) r t * g)) := by
          simp_rw [hFval, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
          rw [hcomm]
          ring
      _ = 0 := by simp [hz]
  have hsplit : ∀ ψ ∈ U, ∀ (t : ℝ) g, (T ψ).1 (splitCentre E (r + s) t * g) = (T ψ).1 g := by
    intro ψ hψ t g
    rw [hTval ψ hψ, hTval ψ hψ]
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 1
    rw [← mul_assoc, ← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t (aT E (r + s) r u), mul_assoc,
      ctn_splitCentre (hSI ψ hψ)]
  have hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ z : ℂ, ∀ ψ ∈ U, cap τ u ψ = z • ψ := by
    intro τ u
    obtain ⟨m, ⟨-, hm⟩, -⟩ := hReg τ
    exact ⟨_, hm u⟩
  refine ⟨T, ⟨hequiv, ⟨φ, hφU, hTφ⟩, ?_, ?_, ?_⟩, hTφ⟩
  · intro ψ hψ x g
    rw [hTval ψ hψ, hTval ψ hψ]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨y, hy⟩ := aT_mul_unip (r + s) r t x
    congr 1
    rw [← mul_assoc, hy, mul_assoc, ctn_unip (hU.2 ψ hψ)]
  · intro ψ hψ k g m₂
    obtain ⟨χ, hχA, hχ⟩ := (F_slicesU U hU.1 hU.2 hsc T hequiv τs a hTval ψ hψ k g).1 m₂
    refine ⟨χ, hχA, hχ, fun t m₁ => ?_, fun r₁ h1 h2 c₁ hc₁ =>
      ⟨ψ, hψ, exp_left hD hFin hr hs ψ (hU.2 ψ hψ) τs a (T ψ).1 (hTval ψ hψ) χ hχA m₂ _ hχ r₁ h1 h2 c₁ hc₁⟩⟩
    have e : lev (Ad E) r s (splitCentre E r t * m₁, m₂) = aT E (r + s) r t * lev (Ad E) r s (m₁, m₂) := by
      rw [show ((splitCentre E r t * m₁, m₂) : GA E r × GA E s) = (splitCentre E r t, 1) * (m₁, m₂) by simp,
        map_mul, splitCentre_eq_aT, lev_aT_left r s r le_rfl]
    rw [hχ, hχ, e, mul_assoc, heig ψ hψ]
  · intro ψ hψ k g m₁
    obtain ⟨χ, hχA, hχ⟩ := (F_slicesU U hU.1 hU.2 hsc T hequiv τs a hTval ψ hψ k g).2 m₁
    refine ⟨χ, hχA, hχ, fun t m₂ => ?_, fun r₂ h1 h2 c₂ hc₂ =>
      ⟨ψ, hψ, exp_right hD hFin hr hs ψ (hU.2 ψ hψ) τs a (T ψ).1 (hTval ψ hψ) c (heig ψ hψ) χ hχA m₁ _ hχ
        r₂ h1 h2 c₂ hc₂⟩⟩
    have e : lev (Ad E) r s (m₁, splitCentre E s t * m₂) =
        splitCentre E (r + s) t * (aT E (r + s) r (-t) * lev (Ad E) r s (m₁, m₂)) := by
      rw [show ((m₁, splitCentre E s t * m₂) : GA E r × GA E s) = (1, splitCentre E s t) * (m₁, m₂) by simp,
        map_mul, splitCentre_eq_aT, lev_aT_right r s s le_rfl, splitCentre_eq_aT, mul_assoc]
    rw [hχ, hχ, e, mul_assoc, hsplit ψ hψ, mul_assoc, heig ψ hψ]
    congr 2
    push_cast
    ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUniqueness

end
end
end
