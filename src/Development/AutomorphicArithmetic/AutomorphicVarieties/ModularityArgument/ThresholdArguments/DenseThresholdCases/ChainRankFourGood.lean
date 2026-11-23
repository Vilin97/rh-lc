module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelRelationTwoX
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.MuRange
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.Module
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.UnrAlgW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ArithmeticPointPurity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.LamDer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrIffSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DOfRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetOfRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GGram

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.MuRange

section

@[expose] public section

open Polynomial TensorProduct UpperTheory.V.Alg UpperTheory.V.J UpperTheory.V.Z.Desc.V0

namespace UpperTheory.V.Z.Desc.V0.GeneralizedEigenRange

section Lin

variable {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

end Lin

section Mu

variable {O Λ B K : Type} [CommRing O] [CommRing Λ] [CommRing B] [Field K] [Algebra O Λ] [Algebra O B]
  (lam : Λ →ₐ[O] B) {M M' : Type} [AddCommGroup M] [Module B M] [Module Λ M]
  [AddCommGroup M'] [Module B M'] [Module Λ M']
  (hs : ∀ (a : Λ) (m : M), a • m = lam a • m) (hs' : ∀ (a : Λ) (m : M'), a • m = lam a • m)

end Mu

end UpperTheory.V.Z.Desc.V0.GeneralizedEigenRange

open UpperTheory.V.Z.Desc.V0.GeneralizedEigenRange

theorem UpperTheory.V.Z.Desc.V0.muRange :
    MuRange := by
  unfold MuRange
  intro O L B K _ _ _ _ _ _ _ _ _ lam J M _ _ _ h e he
  letI : Algebra L B := (lam : L →+* B).toAlgebra
  haveI : IsScalarTower L B M := ⟨fun a b m => by
    rw [Algebra.smul_def, mul_smul, h.hs]
    rfl⟩
  let eB : M →ₗ[B] M :=
    { toFun := e, map_add' := e.map_add, map_smul' := fun b m => he.2 b m }
  let P : Submodule B M := LinearMap.range eB
  have hsP : ∀ (a : L) (m : P), a • m = lam a • m := fun a m => Subtype.ext (h.hs a m.1)
  have hee : ∀ m, e (e m) = e m := fun m => by
    have := congrArg (fun f : Module.End L M => f m) he.1
    simpa using this
  let i : P →ₗ[L] M :=
    { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let s : M →ₗ[L] P :=
    { toFun := fun m => ⟨e m, m, rfl⟩
      map_add' := fun x y => Subtype.ext (e.map_add x y)
      map_smul' := fun a m => Subtype.ext (e.map_smul a m) }
  have hsi : s.comp i = LinearMap.id := by
    ext ⟨x, m, rfl⟩
    exact hee m
  have hie : i.comp s = e := by
    ext m
    rfl
  have hei : e.comp i = i := by
    ext ⟨x, m, rfl⟩
    exact hee m
  haveI := h.free
  haveI := h.fin
  haveI : Module.Projective L P := Module.Projective.of_split i s hsi
  haveI : Module.Finite L P := Module.Finite.of_surjective s (fun x => ⟨i x, by
    rw [← LinearMap.comp_apply, hsi, LinearMap.id_apply]⟩)
  haveI : Module.Free L P := Module.free_of_flat_of_isLocalRing
  let J' : Ideal B := (Module.annihilator B P).radical
  have hD : Dat lam J' P :=
    { hs := hsP
      free := inferInstance
      fin := inferInstance
      rad := Ideal.radical_isRadical _
      supp := fun p hp => hp.radical_le_iff.symm
      tf := by
        rintro c hc a ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [Module.mem_annihilator] at hn ⊢
        intro m
        have h1 := hn m
        rw [mul_pow, mul_smul, ← map_pow, ← hsP] at h1
        exact (smul_eq_zero.mp h1).resolve_left (pow_ne_zero n hc) }
  have hJ : J ≤ J' := by
    have h0 : J ≤ (Module.annihilator B M).radical := by
      rw [Ideal.radical_eq_sInf]
      exact le_sInf fun p hp => (h.supp p hp.2).mp hp.1
    refine h0.trans (Ideal.radical_mono ?_)
    intro b hb
    rw [Module.mem_annihilator] at hb ⊢
    intro m
    exact Subtype.ext (hb m)
  refine ⟨J', P, inferInstance, inferInstance, inferInstance, hD, hJ, fun y => ?_⟩
  letI : Algebra L K := ((y : B →+* K).comp (lam : L →+* B)).toAlgebra
  let F : B → Module.End K (K ⊗[L] M) := fun b => LinearMap.baseChange K (actL lam M h.hs b)
  let G : B → Module.End K (K ⊗[L] P) := fun b => LinearMap.baseChange K (actL lam P hsP b)
  let E : Module.End K (K ⊗[L] M) := LinearMap.baseChange K e
  let ι : K ⊗[L] P →ₗ[K] K ⊗[L] M := LinearMap.baseChange K i
  let σ : K ⊗[L] M →ₗ[K] K ⊗[L] P := LinearMap.baseChange K s
  have hσι : σ.comp ι = LinearMap.id := by
    simp only [σ, ι, ← LinearMap.baseChange_comp, hsi, LinearMap.baseChange_id]
  have hσιa : ∀ w, σ (ι w) = w := fun w => by
    rw [← LinearMap.comp_apply, hσι, LinearMap.id_apply]
  have hinj : Function.Injective ι := fun a b hab => by
    rw [← hσιa a, hab, hσιa]
  have hισ : ι.comp σ = E := by
    simp only [ι, σ, E, ← LinearMap.baseChange_comp, hie]
  have hEι : E.comp ι = ι := by
    simp only [ι, E, ← LinearMap.baseChange_comp, hei]
  have hact : ∀ b, (actL lam M h.hs b).comp i = i.comp (actL lam P hsP b) := fun b => by
    ext
    rfl
  have hFι : ∀ b (μ : K), (F b - μ • 1).comp ι = ι.comp (G b - μ • 1) := fun b μ => by
    rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.smul_comp, LinearMap.comp_smul,
      Module.End.one_eq_id, Module.End.one_eq_id, LinearMap.id_comp, LinearMap.comp_id]
    congr 1
    simp only [F, G, ι, ← LinearMap.baseChange_comp, hact]
  have hpow : ∀ b (μ : K) (k : ℕ) w,
      ((F b - μ • 1) ^ k) (ι w) = ι (((G b - μ • 1) ^ k) w) :=
    fun b μ k w => by
      rw [← LinearMap.comp_apply, Module.End.commute_pow_left_of_commute (hFι b μ) k,
        LinearMap.comp_apply]
  have key : (⨅ b, Module.End.maxGenEigenspace (G b) (y b)).map ι =
      (⨅ b, Module.End.maxGenEigenspace (F b) (y b)) ⊓ Module.End.eigenspace E 1 := by
    ext v
    simp only [Submodule.mem_map, Submodule.mem_inf, Submodule.mem_iInf,
      Module.End.mem_maxGenEigenspace, Module.End.mem_eigenspace_iff, one_smul]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨fun b => ?_, ?_⟩
      · obtain ⟨k, hk⟩ := hw b
        exact ⟨k, by rw [hpow, hk, map_zero]⟩
      · rw [← LinearMap.comp_apply, hEι]
    · rintro ⟨hv, hE⟩
      refine ⟨σ v, fun b => ?_, ?_⟩
      · obtain ⟨k, hk⟩ := hv b
        refine ⟨k, hinj ?_⟩
        rw [← hpow, ← LinearMap.comp_apply ι σ, hισ, hE, hk, map_zero]
      · rw [← LinearMap.comp_apply, hισ, hE]
  have heq : mu lam P hD.hs y = muE lam M h.hs e y := by
    show Module.finrank K ↥(⨅ b, Module.End.maxGenEigenspace (G b) (y b)) =
      Module.finrank K ↥((⨅ b, Module.End.maxGenEigenspace (F b) (y b)) ⊓ Module.End.eigenspace E 1)
    rw [← key]
    exact (Submodule.equivMapOfInjective ι hinj _).finrank_eq
  refine ⟨heq, fun h1 => ?_⟩
  rw [← heq] at h1
  change 1 ≤ Module.finrank K ↥(⨅ b, Module.End.maxGenEigenspace (G b) (y b)) at h1
  have hne : (⨅ b, Module.End.maxGenEigenspace (G b) (y b)) ≠ ⊥ := fun hbot => by
    rw [hbot, finrank_bot] at h1
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rintro a ⟨n, hn⟩
  rw [RingHom.mem_ker]
  by_contra hya
  have hpa : ∀ (n : ℕ) (m : P), (actL lam P hsP a ^ n) m = a ^ n • m := by
    intro n m
    induction n with
    | zero => rw [pow_zero, pow_zero, one_smul]; rfl
    | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, pow_succ', mul_smul]; rfl
  have hGn : (G a) ^ n = 0 := by
    have h2 : actL lam P hsP a ^ n = 0 := by
      ext m
      rw [hpa, LinearMap.zero_apply]
      exact congrArg Subtype.val ((Module.mem_annihilator.mp hn) m)
    simp only [G, ← LinearMap.baseChange_pow, h2, LinearMap.baseChange_zero]
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (Submodule.mem_iInf _ |>.mp hw a)
  set c := y a with hc
  have hX : IsUnit (c⁻¹ • G a - 1) := (IsNilpotent.smul ⟨n, hGn⟩ c⁻¹).isUnit_sub_one
  have hGc : G a - c • 1 = c • (c⁻¹ • G a - 1) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hya, one_smul]
  rw [hGc, _root_.smul_pow, LinearMap.smul_apply] at hk
  have hk2 := (smul_eq_zero.mp hk).resolve_left (pow_ne_zero k hya)
  have hinj2 := (Module.End.isUnit_iff _).mp (hX.pow k)
  exact hw0 (hinj2.1 (by rw [hk2, map_zero]))
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.UnrAlgE

section

@[expose] public section

open UpperTheory.V.Alg UpperTheory.V.J UpperTheory.V.Z.Desc.V0

theorem UpperTheory.V.Z.Desc.V0.unrAlgE :
    UnrAlgW → MuRange → UnrAlgE := by
  intro hW hR O Λ B K _ _ _ _ _ _ _ _ _ _ _ _ _ _ lam J M _ _ _ h e he x 𝒢 b₀ hb₀ hJ h1 hG δ hδ hδJ hδl
  obtain ⟨J', M', _, _, _, h', hJJ', hy⟩ := hR O Λ B K lam J M h e he
  have key : ∀ a, (∀ y ∈ 𝒢, y b₀ ≠ 0 → y a = 0) → a * b₀ ∈ J := by
    intro a ha
    apply hJ
    intro y hy
    rw [map_mul]
    by_cases hb : y b₀ = 0
    · rw [hb, mul_zero]
    · rw [ha y hy hb, zero_mul]
  have hx' : J' ≤ RingHom.ker x := (hy x).2 h1
  have hG1 : ∀ y ∈ 𝒢, y b₀ ≠ 0 → J' ≤ RingHom.ker y := fun y hy1 hb =>
    (hy y).2 (le_trans h1 (hG y hy1 hb))
  refine hW O Λ B K lam J' M' h' x hx' {y | y ∈ 𝒢 ∧ y b₀ ≠ 0} b₀ hb₀ ?_ ?_ δ hδ ?_ hδl
  · intro a ha
    exact hJJ' (key a fun y hy hb => ha y ⟨hy, hb⟩)
  · rintro y ⟨hy1, hb⟩
    refine ⟨hG1 y hy1 hb, ?_⟩
    rw [(hy x).1, (hy y).1]
    exact hG y hy1 hb
  · intro a ha
    have h2 : a * b₀ ∈ J := key a fun y hy hb => RingHom.mem_ker.1 (hG1 y hy hb ha)
    have hxa : x a = 0 := RingHom.mem_ker.1 (hx' ha)
    have h3 : δ (a * b₀) = x a • δ b₀ + x b₀ • δ a := hδ a b₀
    rw [hδJ _ h2, hxa, zero_smul, zero_add, smul_eq_mul] at h3
    exact (mul_eq_zero.1 h3.symm).resolve_left hb₀
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KeepIrrOpenW

section

@[expose] public section




section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr UpperTheory.V.CA Formalism.MainNotions.N
namespace UpperTheory.V.J
theorem irrOpenW_alt : _root_.UpperTheory.V.J.IrrOpenAlt := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B ι J hn hE x hx
  have irr_iff_span {Γ : Type} [Group Γ] (r : Γ →* GL (Fin n) (Qbar l)) :
      IsIrr r ↔ Submodule.span (Qbar l) (Set.range (mat r)) = ⊤ := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [← UpperTheory.V.AlgebraTools.Det.irrIffSpan]
    constructor
    · intro h N hN
      obtain ⟨-, -, hIrr⟩ := h
      exact hIrr N le_top fun g v hv => hN g v hv
    · intro h
      exact ⟨top_ne_bot, fun g v _ => Submodule.mem_top, fun N _ hN => h N fun g v hv => hN g v hv⟩
  have gram_at {A G H K : Type} [CommRing A] [Group G] [Group H] [CommRing K]
      (D : GDet n A G) (f : A →+* K) (φ : H →* G) (ρ : H →* Matrix (Fin n) (Fin n) K)
      (h : (D.map f).comap φ = GDet.ofRep ρ) (g : Fin n × Fin n → H) :
      f (Matrix.det (Matrix.of fun a b => D.tr (MonoidAlgebra.single (φ (g a * g b)) 1))) =
        Matrix.det (Matrix.of fun a b => (ρ (g a) * ρ (g b)).trace) := by
    have trace_at (a : H) : f (D.tr (MonoidAlgebra.single (φ a) 1)) = (ρ a).trace := by
      have hmap : f (D.tr (MonoidAlgebra.single (φ a) 1)) =
          (D.map f).tr (MonoidAlgebra.single (φ a) 1) := by
        have hcoeff := ((d_gmap D).2.2.1 f (MonoidAlgebra.single (φ a) 1)).2 1
        simpa [GDet.tr, MonoidAlgebra.coeff_mapRingHom] using hcoeff.symm
      have hcomap : ((D.map f).comap φ).tr (MonoidAlgebra.single a 1) =
          (D.map f).tr (MonoidAlgebra.single (φ a) 1) := by
        have hchi : ((D.map f).comap φ).chi (MonoidAlgebra.single a 1) =
            (D.map f).chi (MonoidAlgebra.single (φ a) 1) := by
          show (D.map f).D (Polynomial K) (MonoidAlgebra.mapDomainRingHom (Polynomial K) φ
            (MonoidAlgebra.single 1 Polynomial.X -
              MonoidAlgebra.mapRingHom H Polynomial.C (MonoidAlgebra.single a 1))) = _
          congr 1
          rw [map_sub]
          simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
        simp only [GDet.tr, GDet.lam, hchi]
      rw [hmap, ← hcomap, h, ← (d_toDet _ _).2.2.1, d_toDet_ofRep.1 ρ,
        (d_ofRep _ _ _).2.2.1 hn, GDet.repAlg, MonoidAlgebra.lift_single, one_smul]
      congr 1
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rw [trace_at, map_mul]
  obtain ⟨ρ, -, hρ, hirr⟩ := hx
  obtain ⟨m, hm, hdet⟩ := (g_gram _ _ _).1 ((irr_iff_span ρ).1 hirr)
  choose g hg using hm
  refine ⟨Matrix.det (Matrix.of fun a b => B.u.D.tr (MonoidAlgebra.single (V.pr (g a * g b)) 1)), ?_, ?_⟩
  · intro h0
    refine hdet ?_
    have h1 := gram_at B.u.D (x : B.B →+* Qbar l) V.pr (mat ρ) hρ g
    have h2 := h1.symm.trans h0
    simpa only [hg] using h2
  · intro y w hJ hy hy0
    have hA : y.Arith w := ⟨hy.1, fun v j => by
      obtain ⟨ph, hph, -⟩ := hy.2 v
      exact ⟨ph j, hph j⟩⟩
    obtain ⟨ρ', hc', -, hρ', -⟩ := _root_.UpperTheory.GalN.V.end1W' hE y w hJ hA
    refine ⟨ρ', hc', hρ', (irr_iff_span ρ').2 ((g_gram _ _ _).2 ⟨fun a => mat ρ' (g a), fun a => ⟨_, rfl⟩, fun h => hy0 ?_⟩)⟩
    have h1 := gram_at B.u.D (y : B.B →+* Qbar l) V.pr (mat ρ') hρ' g
    exact h1.trans h
end UpperTheory.V.J
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnrE

section

@[expose] public section




section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.HV UpperTheory.V.W
open UpperTheory.V.Z.Desc.V0
theorem UpperTheory.V.Z.Desc.V0.unramified_at_of_dense_purity_num_e_power_series :
    UnrAlgE → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r)
    (ι : Qbar l ≃+* ℂ) (J : Ideal B.B) (m : ℕ), 1 ≤ n → Nonempty (Λ.Λ ≃ₐ[c.O] MvPowerSeries (Fin m) c.O) →
    B.Dense J → B.arithmeticPointPurityDense ι J → NumE B Λ J → UpperTheory.V.J.UnrAt B J := by
  intro hU l _ L Ω _ _ _ _ _ _ s V c n r B Λ ι J m hn hiso hD hE hN
  obtain ⟨M, _, _, _, h, e₀, hId, hmu⟩ := hN
  intro x w hJ hA hI δ hδ hJδ hψ
  obtain ⟨b₀, hb₀, hopen⟩ := _root_.UpperTheory.V.J.irrOpenW_alt l L Ω s V c n r B ι J hn hE x hI
  have hlam := UpperTheory.V.J.lamDer l L Ω s V c n r B Λ x m hiso δ hδ hψ
  have hdense : ∀ a : B.B, (∀ y ∈ {y : B.Pt | J ≤ RingHom.ker y ∧ y.Good w}, y a = 0) → a ∈ J :=
    fun a ha => hD w hA.1 a fun y hy hg => ha y ⟨hy, hg⟩
  have hex : ∃ y : B.Pt, (J ≤ RingHom.ker y ∧ y.Good w) ∧ y b₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hb₀ (hJ (hdense b₀ hcon))
  obtain ⟨y₀, hy₀, hyb₀⟩ := hex
  have hone := (hmu x y₀ w hJ hy₀.1 hA hy₀.2 hI (hopen y₀ w hy₀.1 hy₀.2 hyb₀)).1
  obtain ⟨e⟩ := hiso
  haveI : IsDomain (MvPowerSeries (Fin m) c.O) := GlobalTheory.CohenStructure.isDomain_mvPowerSeries c.O m
  haveI : IsDomain Λ.Λ := e.toRingEquiv.toMulEquiv.isDomain _
  haveI : IsIntegrallyClosed (MvPowerSeries (Fin m) c.O) := GlobalTheory.CohenStructure.isIntegrallyClosed_mvPowerSeries c.O m
  haveI : IsIntegrallyClosed Λ.Λ := IsIntegrallyClosed.of_equiv e.toRingEquiv.symm
  haveI : IsNoetherianRing Λ.Λ := UpperTheory.V.Alg.IsCO.toIsNoetherian (O := c.O)
  haveI : CharZero Λ.Λ := by
    haveI : CharZero c.O :=
      (RingHom.charZero_iff (ϕ := (c.O.val : c.O →ₐ[ℤ_[l]] PadicAlgCl l).toRingHom) Subtype.val_injective).2 inferInstance
    have hC : Function.Injective (MvPowerSeries.C : c.O →+* MvPowerSeries (Fin m) c.O) := fun a b hab => by
      simpa using congrArg MvPowerSeries.constantCoeff hab
    exact (RingHom.charZero_iff (ϕ := (e.symm.toRingEquiv : MvPowerSeries (Fin m) c.O →+* Λ.Λ).comp MvPowerSeries.C)
      (e.symm.injective.comp hC)).1 inferInstance
  exact hU c.O Λ.Λ B.B _ (Λ.toPair B.u) J M h e₀ hId x {y : B.Pt | J ≤ RingHom.ker y ∧ y.Good w} b₀ hb₀ hdense hone
    (fun y hy hyb => (hmu x y w hJ hy.1 hA hy.2 hI (hopen y w hy.1 hy.2 hyb)).2)
    δ hδ hJδ hlam
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ChainRankFourGood

section

@[expose] public section




section
open UpperTheory.V.Z.Desc.V0
theorem UpperTheory.V.J.unramified_algebraic_weights : _root_.UpperTheory.V.J.UnramifiedEndsStatement := _root_.UpperTheory.V.Z.Desc.V0.unramified_at_of_dense_purity_num_e_power_series (unrAlgE unrAlgW muRange)
end
end
end
