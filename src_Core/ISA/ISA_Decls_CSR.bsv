package ISA_Decls_CSR;
// TODO make this `included rather than imported?

typedef enum {
   //CSR_MTVAL,
   //CSR_MCAUSE,
   //CSR_STVAL,
   //CSR_SCAUSE,
   //SCR_DPCC,

   SCR_MTDC,
   SCR_MTCC,
   SCR_MEPCC,
   SCR_MSCRATCHC,
   CSR_MSCRATCH,

   SCR_STDC,
   SCR_STCC,
   SCR_SEPCC,
   SCR_SSCRATCHC,
   CSR_SSCRATCH,

   CSR_DSCRATCH0,
   CSR_DSCRATCH1
} CSR_SCR_RegName deriving (Eq, Bits, FShow);


endpackage
