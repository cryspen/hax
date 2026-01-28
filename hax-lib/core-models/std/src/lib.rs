mod collections {
    mod hash {
        mod map {
            #[hax_lib::opaque]
            struct HashMap<K, V, S>(Option<K>, Option<V>, Option<S>);
            impl<K, V> HashMap<K, V, crate::hash::random::RandomState> {
                fn new() -> HashMap<K, V, crate::hash::random::RandomState> {
                    HashMap(None, None, None)
                }
            }
            // Dummy impl for disambiguator (https://github.com/cryspen/hax/issues/828)
            impl HashMap<usize, usize, usize> {}
            impl<K, V, S> HashMap<K, V, S> {
                fn get<Y>(m: HashMap<K, V, S>, k: K) -> core_models::option::Option<V> {
                    core_models::panicking::internal::panic()
                }
                fn insert(
                    m: HashMap<K, V, S>,
                    k: K,
                    v: V,
                ) -> (HashMap<K, V, S>, core_models::option::Option<V>) {
                    core_models::panicking::internal::panic()
                }
            }
        }
    }
}

mod f64 {
    #[hax_lib::exclude]
    struct f64;
    impl f64 {
        fn powf(x: core::primitive::f64, y: core::primitive::f64) -> core::primitive::f64 {
            core_models::panicking::internal::panic()
        }
    }
}

pub mod hash {
    pub mod random {
        pub struct RandomState;
    }
}

mod io {
    #[hax_lib::attributes]
    pub trait Read {
        // Required method
        #[hax_lib::requires(true)]
        #[hax_lib::ensures(|_| future(buf).len() == buf.len())]
        fn read(&mut self, buf: &mut [u8]) -> Result<usize, error::Error>;

        // Provided methods (not provided in this model as hax doesn't support default methods)
        /* fn read_vectored(&mut self, bufs: &mut [IoSliceMut<'_>]) -> Result<usize>;
        fn is_read_vectored(&self) -> bool;
        fn read_to_end(&mut self, buf: &mut Vec<u8>) -> Result<usize>;
        fn read_to_string(&mut self, buf: &mut String) -> Result<usize>; */
        #[hax_lib::requires(true)]
        #[hax_lib::ensures(|_| future(buf).len() == buf.len())]
        fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), error::Error>;
        /* fn read_buf(&mut self, buf: BorrowedCursor<'_>) -> Result<()>;
        fn read_buf_exact(&mut self, cursor: BorrowedCursor<'_>) -> Result<()>;
        fn by_ref(&mut self) -> &mut Self
        where Self: Sized;
        fn bytes(self) -> Bytes<Self>
        where Self: Sized;
        fn chain<R: Read>(self, next: R) -> Chain<Self, R>
        where Self: Sized;
        fn take(self, limit: u64) -> Take<Self>
        where Self: Sized; */
    }
    #[hax_lib::attributes]
    pub trait Write {
        // Required methods
        #[hax_lib::requires(true)]
        fn write(&mut self, buf: &[u8]) -> Result<usize, error::Error>;
        #[hax_lib::requires(true)]
        fn flush(&mut self) -> Result<(), error::Error>;

        // Provided methods (not provided in this model as hax doesn't support default methods)
        /* fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> Result<usize>;
        fn is_write_vectored(&self) -> bool; */
        #[hax_lib::requires(true)]
        fn write_all(&mut self, buf: &[u8]) -> Result<(), error::Error>;
        /* fn write_all_vectored(&mut self, bufs: &mut [IoSlice<'_>]) -> Result<()>;
        fn write_fmt(&mut self, args: Arguments<'_>) -> Result<()>;
        fn by_ref(&mut self) -> &mut Self
        where Self: Sized; */
    }
    pub mod error {
        pub struct Error;
        pub enum ErrorKind {
            NotFound,
            PermissionDenied,
            ConnectionRefused,
            ConnectionReset,
            HostUnreachable,
            NetworkUnreachable,
            ConnectionAborted,
            NotConnected,
            AddrInUse,
            AddrNotAvailable,
            NetworkDown,
            BrokenPipe,
            AlreadyExists,
            WouldBlock,
            NotADirectory,
            IsADirectory,
            DirectoryNotEmpty,
            ReadOnlyFilesystem,
            FilesystemLoop,
            StaleNetworkFileHandle,
            InvalidInput,
            InvalidData,
            TimedOut,
            WriteZero,
            StorageFull,
            NotSeekable,
            QuotaExceeded,
            FileTooLarge,
            ResourceBusy,
            ExecutableFileBusy,
            Deadlock,
            CrossesDevices,
            TooManyLinks,
            InvalidFilename,
            ArgumentListTooLong,
            Interrupted,
            Unsupported,
            UnexpectedEof,
            OutOfMemory,
            InProgress,
            Other,
        }
        impl Error {
            #[hax_lib::opaque]
            fn kind(&self) -> ErrorKind {
                core_models::panicking::internal::panic()
            }
        }
    }
    mod impls {
        impl super::Read for &[u8] {
            fn read(&mut self, buf: &mut [u8]) -> Result<usize, super::error::Error> {
                let amt = core::cmp::min(buf.len(), self.len());
                let (a, b) = self.split_at(amt);

                buf[..amt].copy_from_slice(a);

                *self = b;
                Ok(amt)
            }
            fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), super::error::Error> {
                if buf.len() > self.len() {
                    // `read_exact` makes no promise about the content of `buf` if it
                    // fails so don't bother about that.
                    *self = &self[self.len()..];
                    return Err(super::error::Error);
                }
                let (a, b) = self.split_at(buf.len());

                buf.copy_from_slice(a);

                *self = b;
                Ok(())
            }
        }
        impl super::Write for Vec<u8> {
            fn write(&mut self, buf: &[u8]) -> Result<usize, super::error::Error> {
                self.extend_from_slice(buf);
                Ok(buf.len())
            }
            fn write_all(&mut self, buf: &[u8]) -> Result<(), super::error::Error> {
                self.extend_from_slice(buf);
                Ok(())
            }
            fn flush(&mut self) -> Result<(), super::error::Error> {
                Ok(())
            }
        }
    }
    mod stdio {
        fn e_print(args: core::fmt::Arguments) {}
    }
}
