module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.IsUnitALMap
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfClassesFrames
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfClasses
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NfAllSmulReB
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.HformSmulRightB
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormOneOfPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.MapMemCSpanOfRat
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NfAllSmulReB
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.MapMemCSpanOfRat
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfClasses
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormalFormAgree
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.BlockActEqBlkRow

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix

section Indep

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem blockAct_eq_blkRow (U : ι → Matrix (Fin n) (Fin n) ℂ) : Formalism.GradedWeylDivisibility.blockAct ℂ U = blkRow U := rfl

theorem isUnit_det_of_on (G o : Matrix (Fin n) (Fin n) ℂ) (h : oᴴ * G * o = 1) : IsUnit o.det := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h1
  have h2 : o.det * (oᴴ.det * G.det) = 1 := by rw [← h1]; ring
  exact ⟨Units.mkOfMulEqOne _ _ h2, rfl⟩

theorem unitary_of_two_on (G o1 o2 : Matrix (Fin n) (Fin n) ℂ) (h1 : o1ᴴ * G * o1 = 1) (h2 : o2ᴴ * G * o2 = 1) :
    (o1⁻¹ * o2) * (o1⁻¹ * o2)ᴴ = 1 ∧ ‖(o1⁻¹ * o2).det‖ = 1 ∧ o2 = o1 * (o1⁻¹ * o2) := by
  have hu1 := isUnit_det_of_on _ _ h1
  have hG : G = (o1ᴴ)⁻¹ * o1⁻¹ := Formalism.L2.Col.eq_of_frame _ _ h1
  have hUU : (o1⁻¹ * o2)ᴴ * (o1⁻¹ * o2) = 1 := by
    have e : (o1⁻¹ * o2)ᴴ * (o1⁻¹ * o2) = o2ᴴ * ((o1ᴴ)⁻¹ * o1⁻¹) * o2 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
      simp only [Matrix.mul_assoc]
    rw [e, ← hG, h2]
  refine ⟨mul_eq_one_comm.1 hUU, ?_, ?_⟩
  · have h := congrArg Matrix.det hUU
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    have h' : ‖(o1⁻¹ * o2).det‖ ^ 2 = 1 := by
      have := congrArg (fun z : ℂ => ‖z‖) h
      simp only [norm_mul, norm_star, norm_one] at this
      rw [sq]; exact this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h'
  · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.one_mul]

theorem term_frame_indep (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) ℂ) (k : ι → ℤ)
    (o1 o2 : ι → Matrix (Fin n) (Fin n) ℂ) (h1 : ∀ τ, (o1 τ)ᴴ * G τ * o1 τ = 1) (h2 : ∀ τ, (o2 τ)ᴴ * G τ * o2 τ = 1)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    (∏ τ, ‖(o1 τ).det‖ ^ (2 * k τ)) * (Formalism.L2.Forms.nfAll lam (subP o1 P) (subP o1 P)).re =
      (∏ τ, ‖(o2 τ).det‖ ^ (2 * k τ)) * (Formalism.L2.Forms.nfAll lam (subP o2 P) (subP o2 P)).re := by
  have hU := fun τ => unitary_of_two_on (G τ) (o1 τ) (o2 τ) (h1 τ) (h2 τ)
  have hc : blkRow (fun τ => (o1 τ)⁻¹ * o2 τ) (blkRow o1 P) = blkRow o2 P := by
    rw [blkRow_comp]
    have e : (fun τ => o1 τ * ((o1 τ)⁻¹ * o2 τ)) = o2 := funext fun τ => ((hU τ).2.2).symm
    rw [e]
  have hsub : subP o2 P = blkRow (fun τ => (o1 τ)⁻¹ * o2 τ) (subP o1 P) := hc.symm
  have hdet : ∀ τ, ‖(o2 τ).det‖ = ‖(o1 τ).det‖ := fun τ => by
    have e := congrArg Matrix.det (hU τ).2.2
    rw [Matrix.det_mul] at e
    rw [e, norm_mul, (hU τ).2.1, mul_one]
  have hn : Formalism.L2.Forms.nfAll lam (subP o2 P) (subP o2 P) = Formalism.L2.Forms.nfAll lam (subP o1 P) (subP o1 P) := by
    rw [hsub, ← blockAct_eq_blkRow]
    exact Formalism.L2.Col.nfAll_blockAct lam _ (fun τ => (hU τ).1) _ _
  rw [hn]
  congr 1
  exact Finset.prod_congr rfl (fun τ _ => by rw [hdet τ])

end Indep

section At

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem frame_on_at (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (ι : D.host.E →+* ℂ)
    (o' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) (ho : o'ᴴ * (gramP D).map ι * o' = 1) :
    (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map ι *
        (bZ u Tf.til.z0).map ι * dOT u o')ᴴ * (gramN D D.R.m le_rfl).map ι *
      (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map ι *
        (bZ u Tf.til.z0).map ι * dOT u o') = 1 := by
  have hga : (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map ι)ᴴ *
      (gramN D D.R.m le_rfl).map ι * ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map ι =
      (gramN D D.R.m le_rfl).map ι := by
    have h := ((Tf.til.ga c)⁻¹).2
    rw [InvMemClass.coe_inv] at h
    have h' : (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map
        (sigD D : D.host.E →+* D.host.E))ᵀ * gramN D D.R.m le_rfl *
        ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) = gramN D D.R.m le_rfl := h
    have h2 := congrArg (fun X => X.map ι) h'
    simp only [Matrix.map_mul] at h2
    rw [map_cT_at] at h2
    exact h2
  have hbZ : ((bZ u Tf.til.z0).map ι)ᴴ * (gramN D D.R.m le_rfl).map ι * (bZ u Tf.til.z0).map ι =
      Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks ((gramP D).map ι) 0 0
        (Matrix.of fun _ _ => ((D.mem u).A.T : ℂ)⁻¹)) := by
    have h := gram_bZ (u := u) Tf.til.z0 Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    have h2 := congrArg (fun X => X.map ι) h
    simp only [Matrix.map_mul] at h2
    rw [map_cT_at] at h2
    rw [h2, Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
    congr 2
    ext i j
    simp [map_inv₀, map_natCast]
  have e : ∀ (X Y Z G : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ),
      (X * Y * Z)ᴴ * G * (X * Y * Z) = Zᴴ * (Yᴴ * (Xᴴ * G * X) * Y) * Z := by
    intro X Y Z G
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hga, hbZ, dOT_on _ _ ho]

end At

end Formalism.L2.GlobalTheoryTheory.Br
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.MapBrTenL

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix

section BC

variable {K K' : Type} [Field K] [Field K'] [CharZero K] [CharZero K'] (j : K →+* K') {ι : Type} [Fintype ι] {N n : ℕ}

theorem map_brStdP (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) (F : Formalism.L2.DIV.Pol K ι N) :
    map j (Formalism.L2.Col.Br.brStdP hN lam sg F : Formalism.L2.DIV.Pol K ι n) =
      (Formalism.L2.Col.Br.brStdP hN lam sg (map j F) : Formalism.L2.DIV.Pol K' ι n) := by
  simp only [Formalism.L2.Col.Br.brStdP, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul]
  rw [MvPolynomial.smul_eq_C_mul, map_mul, map_C, Formalism.L2.Ker.lb_map_projVV, Formalism.L2.Ker.lb_map_coefLast,
    Formalism.L2.Ker.lb_map_brConst, ← MvPolynomial.smul_eq_C_mul]

end BC

section Rec

variable {D : D7} {u : D.what₂.Word}

def brTenL (D : D7) (u : D.what₂.Word) (F : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL) :
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL :=
  (Formalism.L2.Col.Br.brStdP (Nm_succ D.R).symm (lamTr D u) (sgTr D u) F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (D.R.N D.R.m - 1))

theorem map_brTenL (j : D.what₂.LL →+* ℂ) (F : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL) :
    map j (brTenL D u F) = Formalism.L2.Ker.brTen D u (map j F) := by
  unfold brTenL Formalism.L2.Ker.brTen
  rw [map_brStdP, Formalism.L2.Ker.blk_brOne]

end Rec

end Formalism.L2.GlobalTheoryTheory.Br
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.IsUnitBZMap

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix NumberField

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem embS_embLLF : embS D D.what₂.embLL = Formalism.L2.Forms.embT D := by
  funext τ
  apply RingHom.ext
  intro x
  show D.what₂.embLL (D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x)) =
    D.host.φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) x)
  rw [← D.embE_φ₀]
  rfl

theorem pc_rat (Tf : FormsTiedSym D u Ch chOf) (x : Vl D u D.R.m)
    (Pc : (D.mem u).C.cls D.R.m → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL)
    (hPc : ∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
      ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z)) (c' : (D.mem u).C.cls D.R.m) :
    MvPolynomial.map D.what₂.embLL (Pc c') ∈ RatSpan D ((D.fm u).lam D.R.m) := by
  obtain ⟨⟨oN, -⟩, -⟩ := framesAt D u Ch chOf Tf D.what₂.embLL
  rw [embS_embLLF] at oN
  have hx := ((Tf.val D.R.m le_rfl (Or.inr rfl)).rat ((D.fm u).emb D.R.m x)).1 ⟨x, rfl⟩
  obtain ⟨P1, hP1, hP1z⟩ := hx.2 c'
  have hP1e : P1 = MvPolynomial.map D.what₂.embLL (Pc c') := by
    apply Formalism.L2.Col.fnOf_injective _ _ 1 (fun τ => by simp) oN
    funext y
    obtain ⟨z, rfl⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).eY.surjective y
    rw [← hP1z, hPc]
  rw [← hP1e]
  exact hP1

theorem isUnit_bZ_map (Tf : FormsTiedSym D u Ch chOf) (τ : D.what₂.Tau) :
    IsUnit ((bZ u Tf.til.z0).map (Formalism.L2.Forms.embT D τ)).det := by
  have := (bZ_isUnitS Tf).map (Formalism.L2.Forms.embT D τ)
  rw [RingHom.map_det] at this
  exact this



theorem base_eq (Tf : FormsTiedSym D u Ch chOf) (hL : Formalism.L2.Rows.LowerMapTieS Tf) (h : (D.fm u).PRat) (x : Vl D u D.R.m)
    (Pc : (D.mem u).C.cls D.R.m → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL)
    (hPc : ∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
      ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z))
    (Qc : (D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL)
    (hQc : ∀ c, Tf.valP.eW ((D.fm u).ptEmb ((D.fm u).PtL h x)) c =
      fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c))) (c : (D.fm u).clsP) :
    MvPolynomial.map D.what₂.embLL (Qc c) =
      ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c) : ℂˣ) : ℂ))⁻¹ •
        MvPolynomial.map D.what₂.embLL (brTenL D u (PL Tf c (Pc ((D.fm u).til c)))) := by
  classical
  have hB := bZ_isUnitS Tf
  have hmZ := mZ_isUnit hB
  obtain ⟨-, ⟨oP, -⟩⟩ := framesAt D u Ch chOf Tf D.what₂.embLL
  rw [embS_embLLF] at oP
  have hP0 : MvPolynomial.map D.what₂.embLL (Pc ((D.fm u).til c)) ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) :=
    map_mem_CSpan_of_rat _ _ (pc_rat Tf x Pc hPc _) D.what₂.embLL
  let ginv : GL (Fin (D.R.N D.R.m)) D.host.E := ((Tf.til.ga c).1)⁻¹
  let M' : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := atInf (Formalism.L2.Forms.embT D) (ginv : Matrix _ _ D.host.E)
  let A0 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := fun τ => M' τ * (mZ u Tf.til.z0 τ)⁻¹
  have hA0 : ∀ τ, (AL Tf c τ).map D.what₂.embLL = A0 τ := by
    intro τ
    rw [AL_map, embS_embLLF]
    show ((ginv : Matrix _ _ D.host.E) * bZ u Tf.til.z0).map (Formalism.L2.Forms.embT D τ) =
      (ginv : Matrix _ _ D.host.E).map (Formalism.L2.Forms.embT D τ) * (((bZ u Tf.til.z0)⁻¹).map (Formalism.L2.Forms.embT D τ))⁻¹
    rw [Matrix.map_mul, Formalism.L2.Col.map_inv_matrix, Matrix.nonsing_inv_nonsing_inv _ (isUnit_bZ_map Tf τ)]
  have hA0u : ∀ τ, IsUnit (A0 τ).det := fun τ => by rw [← hA0]; exact isUnit_AL_map Tf c _ τ
  have hmapPL : MvPolynomial.map D.what₂.embLL (PL Tf c (Pc ((D.fm u).til c))) =
      (∏ τ, (A0 τ).det ^ shiftOf (lamT u D.R.m) τ) • blkRow A0 (MvPolynomial.map D.what₂.embLL (Pc ((D.fm u).til c))) := by
    rw [map_PL]
    simp only [hA0]
  set χ : ℂ := ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c) : ℂˣ) : ℂ)) with hχ
  have hPbmem : χ⁻¹ • MvPolynomial.map D.what₂.embLL (PL Tf c (Pc ((D.fm u).til c))) ∈
      Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) := by
    rw [hmapPL]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (blkRow_mem_CSpan _ A0 hA0u _ hP0))
  have hPb : ∀ s, Tf.eWz ((D.mem u).P.evz ((D.fm u).emb D.R.m x)) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) (χ⁻¹ • MvPolynomial.map D.what₂.embLL (PL Tf c (Pc ((D.fm u).til c))))
        ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s) := by
    intro s
    rw [Tf.evz ((D.fm u).emb D.R.m x) c s ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm
      (((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s).tr M' (isUnit_det_atInf (Formalism.L2.Forms.embT D) ginv)))]
    · rw [hPc, Equiv.apply_symm_apply, fnOf_trG]
      have e1 : (fun τ => (1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ) τ * M' τ) = M' :=
        funext fun τ => by simp
      rw [e1, fnOf_change _ _ (mZ u Tf.til.z0) M' hmZ, hmapPL]
      simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Units.val_inv_eq_inv_val]
      rfl
    · intro τ
      simp only [Equiv.apply_symm_apply]
      show ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s).1 τ =
        atInf (Formalism.L2.Forms.embT D) (Tf.til.ga c).1.1 τ * (M' τ * ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s).1 τ)
      rw [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]
  have h3 := hL hB ((D.mem u).P.evz ((D.fm u).emb D.R.m x)) c _ hPbmem hPb
  have h4 : fnOf (gramC (gramP D) (Formalism.L2.Forms.embT D)) (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c)) =
      fnOf (gramC (gramP D) (Formalism.L2.Forms.embT D)) (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u (χ⁻¹ • MvPolynomial.map D.what₂.embLL (PL Tf c (Pc ((D.fm u).til c))))) := by
    rw [← hQc c, (D.fm u).PtL_spec h x, h3]
  have h5 := Formalism.L2.Col.fnOf_injective _ _ 1 (fun τ => by simp) oP h4
  rw [h5, map_smul, map_brTenL]

end Formalism.L2.GlobalTheoryTheory.Br
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfTorsionCharacter

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix NumberField
open scoped ComplexOrder



theorem normClsAt_of_tors (hT : ChiTors) : NormClsAt := by
  intro D u Ch chOf Tf hL hBe h s x Pc hPc Qc hQc o ho o' ho' c
  classical
  have hbase := base_eq Tf hL h x Pc hPc Qc hQc c
  obtain ⟨k, hk, hχ⟩ := hT D u Ch chOf Tf c
  obtain ⟨a, ha, has⟩ := desc_scalar D.what₂.embLL (Qc c) (brTenL D u (PL Tf c (Pc ((D.fm u).til c)))) _ k hk hχ hbase
  have hAsu : ∀ τ, IsUnit ((AL Tf c τ).map s).det := fun τ => isUnit_AL_map Tf c s τ
  have hR : MvPolynomial.map s (Pc ((D.fm u).til c)) ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) :=
    map_mem_CSpan_of_rat _ _ (pc_rat Tf x Pc hPc _) s
  have hY := blkRow_mem_CSpan _ (fun τ => (AL Tf c τ).map s) hAsu _ hR
  have hQs : MvPolynomial.map s (Qc c) = (s a * ∏ τ, ((AL Tf c τ).map s).det ^ shiftOf (lamT u D.R.m) τ) •
      Formalism.L2.Ker.brTen D u (blkRow (fun τ => (AL Tf c τ).map s) (MvPolynomial.map s (Pc ((D.fm u).til c)))) := by
    rw [ha, MvPolynomial.smul_eq_C_mul, map_mul, map_C, map_brTenL, map_PL, map_smul, ← MvPolynomial.smul_eq_C_mul,
      smul_smul]
  have hoN : ∀ τ, (o.1 τ)ᴴ * gramC (gramN D D.R.m le_rfl) (embS D s) τ * o.1 τ = 1 := fun τ =>
    Formalism.L2.Col.frame_pos o ho τ (gramN_posDef_at Tf (embS D s τ)).posSemidef
  have hoP : ∀ τ, (o'.1 τ)ᴴ * gramC (gramP D) (embS D s) τ * o'.1 τ = 1 := fun τ =>
    Formalism.L2.Col.frame_pos o' ho' τ (gramP_posDef_at Tf (embS D s τ)).posSemidef
  have hon : ∀ τ, ((AL Tf c τ).map s * dOT u (o'.1 τ))ᴴ * gramC (gramN D D.R.m le_rfl) (embS D s) τ *
      ((AL Tf c τ).map s * dOT u (o'.1 τ)) = 1 := by
    intro τ
    rw [AL_map, Matrix.map_mul]
    exact frame_on_at Tf c (embS D s τ) (o'.1 τ) (hoP τ)
  have hind := term_frame_indep ((D.fm u).lam D.R.m) (gramC (gramN D D.R.m le_rfl) (embS D s)) (shiftOf (lamT u D.R.m)) o.1
    (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) hoN hon (MvPolynomial.map s (Pc ((D.fm u).til c)))
  have hchain := chain_at Tf hBe o'.1 o'.2 _ hY
  have hcomp : blkRow (fun τ => dOT u (o'.1 τ)) (blkRow (fun τ => (AL Tf c τ).map s) (MvPolynomial.map s (Pc ((D.fm u).til c)))) =
      subP (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) (MvPolynomial.map s (Pc ((D.fm u).til c))) := blkRow_comp _ _ _
  rw [hcomp] at hchain
  rw [hQs, map_smul, nfAll_smul_reB, normal_form_agree, hind]
  have hdet : ∏ τ, ‖((AL Tf c τ).map s * dOT u (o'.1 τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ) =
      (∏ τ, ‖((AL Tf c τ).map s).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
        ∏ τ, ‖(dOT u (o'.1 τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_mul, norm_mul, mul_zpow]
  have hκ : ‖s a * ∏ τ, ((AL Tf c τ).map s).det ^ shiftOf (lamT u D.R.m) τ‖ ^ 2 =
      ‖s a‖ ^ 2 * ∏ τ, ‖((AL Tf c τ).map s).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ) := by
    rw [norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [norm_zpow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm (shiftOf (lamT u D.R.m) τ)]
    norm_num
  rw [hdet, hκ]
  have hsa : ‖s a‖ ^ 2 ≤ 1 := by
    have h1 := has s
    have h0 := norm_nonneg (s a)
    nlinarith
  set nW := (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (Formalism.L2.Ker.brTen D u (blkRow (fun τ => (AL Tf c τ).map s)
    (MvPolynomial.map s (Pc ((D.fm u).til c)))))) (subP o'.1 (Formalism.L2.Ker.brTen D u (blkRow (fun τ => (AL Tf c τ).map s)
    (MvPolynomial.map s (Pc ((D.fm u).til c))))))).re with hnW
  set K2 := ∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)
  set KA := ∏ τ, ‖((AL Tf c τ).map s).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)
  have hKA : 0 ≤ KA := Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _
  have hK2 : 0 ≤ K2 := Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _
  have hnW : 0 ≤ nW := Formalism.L2.Ker.ta_nfAll_nonneg _ _
  calc K2 * (‖s a‖ ^ 2 * KA * nW) = ‖s a‖ ^ 2 * (KA * (K2 * nW)) := by ring
    _ ≤ 1 * (KA * (ptB D u * ((∏ τ, ‖(dOT u (o'.1 τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
          (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) (subP (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) (MvPolynomial.map s (Pc ((D.fm u).til c))))
            (subP (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) (MvPolynomial.map s (Pc ((D.fm u).til c))))).re))) :=
        mul_le_mul hsa (mul_le_mul_of_nonneg_left hchain hKA) (mul_nonneg hKA (mul_nonneg hK2 hnW)) zero_le_one
    _ = _ := by ring

end Formalism.L2.GlobalTheoryTheory.Br
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfInjectiveStable

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

theorem chiTors : ChiTors := by
  intro D u Ch chOf Tf c
  classical
  let P : ℂ → Prop := fun z => ∃ k : ℕ, 0 < k ∧ z ^ k = 1
  have h1 : P 1 := ⟨1, one_pos, one_pow _⟩
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨k, hk, hx⟩ ⟨l, hl, hy⟩
    refine ⟨k * l, Nat.mul_pos hk hl, ?_⟩
    rw [mul_pow, pow_mul, hx, one_pow, one_mul, mul_comm k l, pow_mul, hy, one_pow]
  have hfac : ∀ a v h, P (((Tf.lamM a v h ((Tf.glevM).red a v h (Tf.tilAd.ka c)) : ℂˣ) : ℂ))⁻¹ := by
    intro a v h
    haveI : Finite (Formalism.L2.Forms.kv D.host.F v) := Formalism.UG.P.glint_finite_residueField v
    refine ⟨orderOf ((Tf.glevM).red a v h (Tf.tilAd.ka c)), orderOf_pos _, ?_⟩
    rw [inv_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one, inv_one]
  show P _
  rw [(Tf.glevM).chi_eq]
  refine Finset.prod_induction _ P hmul h1 fun a _ => ?_
  refine finprod_induction P h1 hmul fun v => ?_
  exact finprod_induction P h1 hmul fun h => hfac a v h

theorem normClsAt_holds : NormClsAt := normClsAt_of_tors chiTors

theorem norm_bound_of_injective_stable (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) : NormBoundAtInfinity :=
  norm_bound_of_classes h1 h2 normClsAt_holds

end Formalism.L2.GlobalTheoryTheory.Br
end
end
end
