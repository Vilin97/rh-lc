module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCosetProductsCommuteSplitPlaceStatement
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalAtPlaceConjProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharEqOneInertPrimeOffLevel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitHeckeElementLabelZerosThenNegOnes
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.RingTheory.PicardGroup

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalAtPlaceConjProductStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isLocalAtPlace_conj_product : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i i' : ok × ℕ) (a b c d : Bridge.Gf V), (pl i.1).under (𝓞 D.host.F) = (pl i'.1).under (𝓞 D.host.F) → isLocEnv V pl ok i a → isLocEnv V pl ok i' b → isLocEnv V pl ok i' c → isLocEnv V pl ok i d → isLocEnv V pl ok i ((c * d)⁻¹ * (a * b)) := by
  first | exact @GlobalTheory.FrameProdLoc.isLocEnv_prod | exact GlobalTheory.FrameProdLoc.isLocEnv_prod | (intros; apply GlobalTheory.FrameProdLoc.isLocEnv_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelElementLocalCoprimeActsTrivially

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

namespace GlobalTheory.FrameTriv

theorem map_eq_one_of_isLocEnv {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → HeightOneSpectrum (𝓞 D.host.E)) (ok : Set Pl0)
    (i : ok × ℕ) (x : Bridge.Gf V) (hloc : isLocEnv V pl ok i x) (l : ℕ) (hl : (l : 𝓞 D.host.E) ∉ (pl i.1).asIdeal)
    {R : Type} [CommRing R] (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* R)
    (hev : ∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F,
      (∀ v : HeightOneSpectrum (𝓞 D.host.F), (l : 𝓞 D.host.F) ∈ v.asIdeal → a v = 0) → ev (a ⊗ₜ[D.host.F] 1) = 0) :
    (x.1.val : Matrix (Fin V.rank) (Fin V.rank) ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E)).map ev = 1 := by
  obtain ⟨e, α, he, -, hS, hx⟩ := hloc
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, hε, hf⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ (Or.inl ⟨he, rfl⟩)
  obtain ⟨εf, hεf, -, h0⟩ := hε
  have hvan : ev (εf ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 := by
    refine hev εf fun v' hv' => h0 v' ?_
    rintro rfl
    apply hl
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ (pl i.1).asIdeal := hv'
    rwa [map_natCast] at h2
  let φ : Formalism.L2.Theta.AE D →+* (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hmat : ∀ a c, x.1.val a c = φ ((Formalism.L2.Theta.mt V α) a c) := by
    intro a c
    rw [hx]
    rfl
  have hφε : φ (algebraMap _ (Formalism.L2.Theta.AE D) ε) = εf ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [hεf]
    rfl
  let ψ : Formalism.L2.Theta.AE D →+* R := ev.comp φ
  have hψ : ψ (algebraMap _ (Formalism.L2.Theta.AE D) ε) = 0 := (congrArg ev hφε).trans hvan
  ext a c
  have hsplit : Formalism.L2.Theta.mt V α a c =
      algebraMap _ (Formalism.L2.Theta.AE D) ε * (Formalism.L2.Theta.mt V α - 1) a c + (1 : Matrix _ _ (Formalism.L2.Theta.AE D)) a c := by
    rw [← hf, hS a c, Matrix.sub_apply, sub_add_cancel]
  refine (congrArg ev (hmat a c)).trans ?_
  show ψ _ = _
  rw [hsplit, map_add ψ, ψ.map_mul, hψ, zero_mul, zero_add, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact ψ.map_one
  · exact ψ.map_zero

theorem intEmb_injective {l : ℕ} [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)) : Function.Injective (intEmb Lf) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem kap_eq_one {O K : Type} [CommRing O] [CommRing K] {f : O →+* K} (hf : Function.Injective f) {N n : ℕ} (g : GL (Fin N) O)
    (b : GL (Fin N) K) (M : Matrix (Fin n) (Fin n) K) (rk : Fin N → Fin n) (hrk : Function.Injective rk) (hM : M = 1)
    (h : (Matrix.GeneralLinearGroup.map f g).val = (b⁻¹).val * M.submatrix rk rk * b.val) : g = 1 := by
  rw [hM, Matrix.submatrix_one _ hrk, mul_one, Units.inv_mul] at h
  refine Units.ext (Matrix.ext fun a c => hf ?_)
  have h3 : f (g.val a c) = (1 : Matrix (Fin N) (Fin N) K) a c := congrFun (congrFun h a) c
  rw [h3, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact f.map_one.symm
  · exact f.map_zero.symm

theorem chi_eq_one {O K ι : Type} [CommRing O] [Field K] [Fintype ι] {f : O →+* K} (hf : Function.Injective f) {N : ℕ}
    (io : K ≃+* ℂ) (g : ι → GL (Fin N) O) (sh : ι → ℤ) (x : Oˣ) (y : ℂˣ) (hg : g = 1) (hy : y = 1)
    (h : io (f x * ∏ τ, f (g τ).val.det ^ sh τ) * (y : ℂ) = 1) : x = 1 := by
  subst hg hy
  simp only [Pi.one_apply, Units.val_one, Matrix.det_one, map_one, one_zpow, Finset.prod_const_one, mul_one] at h
  refine Units.ext (hf (io.injective ?_))
  rw [h, Units.val_one, map_one, map_one]



theorem triv_of_isLocEnv : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] {N : ℕ} (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ) (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ) (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf] (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ), ChoiceOk p j w e0 b io ev bs rk sh kap chi → ∀ (i : (blk p j (p.R.mu w)).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) i.1).asIdeal → ∀ u : Bridge.Gf (Vc D j), u ∈ levJ p j (p.R.mu w) → isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i u → (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) N Lf kap chi).Triv u := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j w _ N e0 b io ev bs rk sh Lf _ kap chi hC i hi1 hi2 hl u hu hloc
  obtain ⟨-, -, -, hEv, hKap, hChi⟩ := hC
  have hc : levChi p j (p.R.mu w) ⟨u, hu⟩ = 1 := (p.R.B.L j (p.R.mu w)).hecke.chi_loc i ⟨hi1, hi2⟩ ⟨u, hu⟩ hloc
  have hone : ∀ τ, (matOf j u).map (ev τ) = 1 := fun τ =>
    map_eq_one_of_isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i u hloc (Formalism.EigenvalueLevelCeiling.plc w) hl (ev τ) (hEv τ).2.2.1
  have hk : kap ⟨u, hu⟩ = 1 := funext fun τ =>
    kap_eq_one (intEmb_injective Lf) (kap ⟨u, hu⟩ τ) (bs τ) ((matOf j u).map (ev τ)) rk rk.injective (hone τ) (hKap ⟨u, hu⟩ τ)
  have hx : chi ⟨u, hu⟩ = 1 :=
    chi_eq_one (intEmb_injective Lf) io (kap ⟨u, hu⟩) sh (chi ⟨u, hu⟩) (levChi p j (p.R.mu w) ⟨u, hu⟩) hk hc (hChi ⟨u, hu⟩)
  exact ⟨hu, hk, hx⟩

end GlobalTheory.FrameTriv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelElementLocalCoprimeActsTriviallyStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.levelElement_local_coprime_acts_trivially : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] {N : ℕ} (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ) (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ) (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf] (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ), ChoiceOk p j w e0 b io ev bs rk sh kap chi → ∀ (i : (blk p j (p.R.mu w)).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) i.1).asIdeal → ∀ u : Bridge.Gf (Vc D j), u ∈ levJ p j (p.R.mu w) → isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i u → (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) N Lf kap chi).Triv u := by
  first | exact @GlobalTheory.FrameTriv.triv_of_isLocEnv | exact GlobalTheory.FrameTriv.triv_of_isLocEnv | (intros; apply GlobalTheory.FrameTriv.triv_of_isLocEnv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalElementsCommuteDistinctFinitePlaces

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocComm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem ext_cmp {z₁ z₂ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E}
    (h : ∀ w, GlobalTheory.HeckeRowsCompare.cmp D w z₁ = GlobalTheory.HeckeRowsCompare.cmp D w z₂) : z₁ = z₂ := by
  refine (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (Module.finBasis D.host.F D.host.E)).ext_elem fun i => ?_
  refine FiniteAdeleRing.ext _ fun w => ?_
  have e := congrArg (fun z => (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F w)
    (Module.finBasis D.host.F D.host.E)).repr z i) (h w)
  simp only [GlobalTheory.HeckeRowsCompare.cmp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at e
  rw [GlobalTheory.HeckeRowsCompare.repr_map, GlobalTheory.HeckeRowsCompare.repr_map] at e
  exact e

theorem mul_comm_of_locAt (V : Formalism.BasicNotions.TH.HSp D) {v v' : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ≠ v') {x y : Bridge.Gf V}
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v x) (hy : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v' y) : x * y = y * x := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply ext_cmp
  intro w
  have hm : ∀ a b : Bridge.Gf V,
      GlobalTheory.HeckeRowsCompare.cmp D w ((a * b : Bridge.Gf V).1.1 i j) =
        ((a.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w)) * (b.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w))) i j := by
    intro a b
    rw [← Matrix.map_mul]
    rfl
  show GlobalTheory.HeckeRowsCompare.cmp D w ((x * y : Bridge.Gf V).1.1 i j) = GlobalTheory.HeckeRowsCompare.cmp D w ((y * x : Bridge.Gf V).1.1 i j)
  rw [hm, hm]
  by_cases hw : w = v
  · subst hw
    have h1 : y.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w) = 1 := hy w hv
    rw [h1, mul_one, one_mul]
  · have h1 : x.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w) = 1 := hx w hw
    rw [h1, mul_one, one_mul]

theorem mul_comm_of_isLocEnv : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i i' : ok × ℕ)
    (x y : Bridge.Gf V), (pl i.1).under (𝓞 D.host.F) ≠ (pl i'.1).under (𝓞 D.host.F) → isLocEnv V pl ok i x →
      isLocEnv V pl ok i' y → x * y = y * x := by
  intro D V Pl0 pl ok i i' x y hv hx hy
  exact mul_comm_of_locAt V hv
    (GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ x ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i x).2.1 hx))
    (GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ y ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i' y).2.1 hy))

end GlobalTheory.LocComm

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalElementsCommuteDistinctFinitePlacesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.localElements_commute_distinct_realPlaces : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i i' : ok × ℕ) (x y : Bridge.Gf V), (pl i.1).under (𝓞 D.host.F) ≠ (pl i'.1).under (𝓞 D.host.F) → isLocEnv V pl ok i x → isLocEnv V pl ok i' y → x * y = y * x := by
  first | exact @GlobalTheory.LocComm.mul_comm_of_isLocEnv | exact GlobalTheory.LocComm.mul_comm_of_isLocEnv | (intros; apply GlobalTheory.LocComm.mul_comm_of_isLocEnv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutationAtSmallPlace

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeCommFrame


open Classical in
theorem exists_equiv_of_fibre_card {G : Type} [Group G] (K : Subgroup G) (A B : Finset G) (Tr : G → Prop)
    (hcount : ∀ c : G ⧸ K, ((A ×ˢ B).filter (fun x => ((x.1 * x.2 : G) : G ⧸ K) = c)).card =
      ((B ×ˢ A).filter (fun x => ((x.1 * x.2 : G) : G ⧸ K) = c)).card)
    (htr : ∀ s ∈ A, ∀ t ∈ B, ∀ t' ∈ B, ∀ s' ∈ A, (t' * s')⁻¹ * (s * t) ∈ K → Tr ((t' * s')⁻¹ * (s * t))) :
    ∃ σ : A × B ≃ B × A, ∀ x, Tr ((((σ x).1 : G) * (σ x).2)⁻¹ * ((x.1 : G) * x.2)) := by
  classical
  have fib : ∀ (A B : Finset G) (c : G ⧸ K),
      Fintype.card {x : A × B // (((x.1 : G) * x.2 : G) : G ⧸ K) = c} =
        ((A ×ˢ B).filter (fun x => ((x.1 * x.2 : G) : G ⧸ K) = c)).card := by
    intro A B c
    rw [← Fintype.card_coe]
    exact Fintype.card_congr
      { toFun := fun x => ⟨((x.1.1 : G), (x.1.2 : G)), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨x.1.1.2, x.1.2.2⟩, x.2⟩⟩
        invFun := fun y => ⟨(⟨y.1.1, (Finset.mem_product.1 (Finset.mem_filter.1 y.2).1).1⟩,
          ⟨y.1.2, (Finset.mem_product.1 (Finset.mem_filter.1 y.2).1).2⟩), (Finset.mem_filter.1 y.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  let f : A × B → G ⧸ K := fun x => (((x.1 : G) * x.2 : G) : G ⧸ K)
  let g : B × A → G ⧸ K := fun x => (((x.1 : G) * x.2 : G) : G ⧸ K)
  have e : ∀ c, {x // f x = c} ≃ {y // g y = c} := fun c =>
    Fintype.equivOfCardEq (by rw [fib A B c, fib B A c]; convert hcount c)
  refine ⟨Equiv.ofFiberEquiv e, fun x => ?_⟩
  have h := Equiv.ofFiberEquiv_map e x
  have hK : (((Equiv.ofFiberEquiv e x).1 : G) * (Equiv.ofFiberEquiv e x).2)⁻¹ * ((x.1 : G) * x.2) ∈ K :=
    QuotientGroup.eq.1 h
  exact htr _ x.1.2 _ x.2.2 _ (Equiv.ofFiberEquiv e x).1.2 _ (Equiv.ofFiberEquiv e x).2.2 hK

theorem commAt_of {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
    (j : Fin D.R.m) (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : CommAt p j P w := by
  intro _ e0 b io ev bs rk sh Lf _ kap chi hc F i i'
  have hN : P.Nr = (Vc D j).rank := by simpa using Fintype.card_congr rk.toEquiv
  have hi1 : 1 ≤ i.1.2 := i.2.1
  have hi2 : i.1.2 ≤ (Vc D j).rank := hN ▸ i.2.2.1
  have hi1' : 1 ≤ i'.1.2 := i'.2.1
  have hi2' : i'.1.2 ≤ (Vc D j).rank := hN ▸ i'.2.2.1
  have hA := (p.R.B.L j (p.R.mu w)).hecke.hA_loc i.1 ⟨hi1, hi2⟩
  have hA' := (p.R.B.L j (p.R.mu w)).hecke.hA_loc i'.1 ⟨hi1', hi2'⟩
  by_cases hv : (plOf p j (p.R.mu w) i.1.1).under (𝓞 D.host.F) = (plOf p j (p.R.mu w) i'.1.1).under (𝓞 D.host.F)
  · exact exists_equiv_of_fibre_card (levJ p j (p.R.mu w)) (hkA p j (p.R.mu w) i.1) (hkA p j (p.R.mu w) i'.1) F.Triv
      (GlobalTheory.T.heckeCosetProducts_commute_splitPlace p j (p.R.mu w) i.1 i'.1 hi1 hi2 hi1' hi2' hv)
      (fun s hs t ht t' ht' s' hs' hK => GlobalTheory.T.levelElement_local_coprime_acts_trivially p j w e0 b io ev bs rk sh Lf kap chi hc i.1 hi1 hi2 i.2.2.2 _ hK
        (GlobalTheory.T.isLocalAtPlace_conj_product (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i.1 i'.1 s t t' s' hv (hA s hs) (hA' t ht) (hA' t' ht') (hA s' hs')))
  · refine ⟨Equiv.prodComm _ _, fun x => ?_⟩
    have hcomm : (x.1 : F.G) * (x.2 : F.G) = (x.2 : F.G) * (x.1 : F.G) :=
      GlobalTheory.T.localElements_commute_distinct_realPlaces (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i.1 i'.1 (x.1 : F.G) (x.2 : F.G) hv (hA _ x.1.2) (hA' _ x.2.2)
    show F.Triv (((x.2 : F.G) * (x.1 : F.G))⁻¹ * ((x.1 : F.G) * (x.2 : F.G)))
    rw [hcomm, inv_mul_cancel]
    exact ⟨one_mem _, map_one _, map_one _⟩

end GlobalTheory.HeckeCommFrame

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Comm

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeckeCommFrame
theorem comm_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → CommAt p j P w :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun _ _ _ p _ _ j P _ _ _ w _ _ _ => commAt_of p j P w⟩⟩
end GlobalTheory.HeckeCommFrame
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CommStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.commAt_of_smallAt_in_range : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → CommAt p j P w := by
  first | exact @_root_.GlobalTheory.HeckeCommFrame.comm_alt | exact _root_.GlobalTheory.HeckeCommFrame.comm_alt | (intros; apply _root_.GlobalTheory.HeckeCommFrame.comm_alt <;> assumption)
end
end
end
