module Std.Io.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Error = | Error : t_Error

type t_ErrorKind =
  | ErrorKind_NotFound : t_ErrorKind
  | ErrorKind_PermissionDenied : t_ErrorKind
  | ErrorKind_ConnectionRefused : t_ErrorKind
  | ErrorKind_ConnectionReset : t_ErrorKind
  | ErrorKind_HostUnreachable : t_ErrorKind
  | ErrorKind_NetworkUnreachable : t_ErrorKind
  | ErrorKind_ConnectionAborted : t_ErrorKind
  | ErrorKind_NotConnected : t_ErrorKind
  | ErrorKind_AddrInUse : t_ErrorKind
  | ErrorKind_AddrNotAvailable : t_ErrorKind
  | ErrorKind_NetworkDown : t_ErrorKind
  | ErrorKind_BrokenPipe : t_ErrorKind
  | ErrorKind_AlreadyExists : t_ErrorKind
  | ErrorKind_WouldBlock : t_ErrorKind
  | ErrorKind_NotADirectory : t_ErrorKind
  | ErrorKind_IsADirectory : t_ErrorKind
  | ErrorKind_DirectoryNotEmpty : t_ErrorKind
  | ErrorKind_ReadOnlyFilesystem : t_ErrorKind
  | ErrorKind_FilesystemLoop : t_ErrorKind
  | ErrorKind_StaleNetworkFileHandle : t_ErrorKind
  | ErrorKind_InvalidInput : t_ErrorKind
  | ErrorKind_InvalidData : t_ErrorKind
  | ErrorKind_TimedOut : t_ErrorKind
  | ErrorKind_WriteZero : t_ErrorKind
  | ErrorKind_StorageFull : t_ErrorKind
  | ErrorKind_NotSeekable : t_ErrorKind
  | ErrorKind_QuotaExceeded : t_ErrorKind
  | ErrorKind_FileTooLarge : t_ErrorKind
  | ErrorKind_ResourceBusy : t_ErrorKind
  | ErrorKind_ExecutableFileBusy : t_ErrorKind
  | ErrorKind_Deadlock : t_ErrorKind
  | ErrorKind_CrossesDevices : t_ErrorKind
  | ErrorKind_TooManyLinks : t_ErrorKind
  | ErrorKind_InvalidFilename : t_ErrorKind
  | ErrorKind_ArgumentListTooLong : t_ErrorKind
  | ErrorKind_Interrupted : t_ErrorKind
  | ErrorKind_Unsupported : t_ErrorKind
  | ErrorKind_UnexpectedEof : t_ErrorKind
  | ErrorKind_OutOfMemory : t_ErrorKind
  | ErrorKind_InProgress : t_ErrorKind
  | ErrorKind_Other : t_ErrorKind

val t_ErrorKind_cast_to_repr (x: t_ErrorKind)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

val impl_Error__kind (self: t_Error) : Prims.Pure t_ErrorKind Prims.l_True (fun _ -> Prims.l_True)
