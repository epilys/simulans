// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

use std::sync::{
    mpsc::{channel, Receiver},
    Arc, Mutex,
};

use nix::{
    fcntl::{fcntl, FcntlArg},
    sys::termios::{tcgetattr, tcsetattr, Termios},
};

#[derive(Clone)]
pub struct CharBackendWriter {
    #[allow(clippy::type_complexity)]
    pub write_all: Arc<dyn Fn(&[u8]) + Sync + Send>,
}

impl std::fmt::Debug for CharBackendWriter {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        fmt.debug_struct("CharBackendWriter")
            .finish_non_exhaustive()
    }
}

struct StdioFrontend {
    oldtty: Option<(Termios, i32, i32)>,
}

enum Frontend {
    #[allow(dead_code)]
    Stdio(StdioFrontend),
    Sink,
}

pub struct CharBackend {
    pub writer: CharBackendWriter,
    pub receiver: Receiver<Vec<u8>>,
    #[allow(dead_code)]
    frontend: Frontend,
}

impl Drop for StdioFrontend {
    fn drop(&mut self) {
        let Some((oldtty, old_fd0_flags, old_fd1_flags)) = self.oldtty.take() else {
            return;
        };

        let stdin = std::io::stdin();
        let stdout = std::io::stdout();

        _ = tcsetattr(&stdin, nix::sys::termios::SetArg::TCSANOW, &oldtty);
        _ = fcntl(
            &stdin,
            FcntlArg::F_SETFL(nix::fcntl::OFlag::from_bits(old_fd0_flags).unwrap()),
        );
        _ = fcntl(
            &stdout,
            FcntlArg::F_SETFL(nix::fcntl::OFlag::from_bits(old_fd1_flags).unwrap()),
        );
    }
}

impl CharBackend {
    pub fn new_stdio() -> Self {
        let mut stdin = std::io::stdin();
        let stdout = std::io::stdout();
        let old_fd0_flags = fcntl(&stdin, FcntlArg::F_GETFL).unwrap();
        let old_fd1_flags = fcntl(&stdout, FcntlArg::F_GETFL).unwrap();
        let oldtty = tcgetattr(&stdin).unwrap();
        {
            use nix::sys::termios::{ControlFlags, InputFlags, LocalFlags, OutputFlags};

            let mut tty = oldtty.clone();
            tty.input_flags &= !(InputFlags::IGNBRK
                | InputFlags::BRKINT
                | InputFlags::PARMRK
                | InputFlags::ISTRIP
                | InputFlags::INLCR
                | InputFlags::IGNCR
                | InputFlags::ICRNL
                | InputFlags::IXON);
            tty.output_flags |= OutputFlags::OPOST;
            tty.local_flags &=
                !(LocalFlags::ECHO | LocalFlags::ECHONL | LocalFlags::ICANON | LocalFlags::IEXTEN);
            tty.control_flags &= !(ControlFlags::CSIZE | ControlFlags::PARENB);
            tty.control_flags |= ControlFlags::CS8;
            tty.control_chars[nix::sys::termios::SpecialCharacterIndices::VMIN as usize] = 1;
            tty.control_chars[nix::sys::termios::SpecialCharacterIndices::VTIME as usize] = 0;

            tcsetattr(&stdin, nix::sys::termios::SetArg::TCSANOW, &tty).unwrap();
        }
        let (sender, receiver) = channel();
        std::thread::Builder::new()
            .name("input".into())
            .spawn(move || {
                use std::io::Read;

                let mut char = [0; 32];
                while let Ok(n) = stdin.read(&mut char) {
                    if n > 0 {
                        sender.send(char[0..n].to_vec()).unwrap();
                    }
                }
            })
            .unwrap();

        Self {
            writer: CharBackendWriter {
                write_all: Arc::new({
                    move |buf| {
                        use std::io::Write;

                        let mut stdout = stdout.lock();
                        stdout.write_all(buf).unwrap();
                        stdout.flush().unwrap();
                    }
                }),
            },
            receiver,
            frontend: Frontend::Stdio(StdioFrontend {
                oldtty: Some((oldtty, old_fd0_flags, old_fd1_flags)),
            }),
        }
    }

    pub fn new_sink(buffer: Arc<Mutex<Vec<u8>>>) -> Self {
        let (_sender, receiver) = channel();

        Self {
            writer: CharBackendWriter {
                write_all: Arc::new({
                    move |buf| {
                        use std::io::Write;

                        let mut buffer = buffer.lock().unwrap();
                        buffer.write_all(buf).unwrap();
                    }
                }),
            },
            receiver,
            frontend: Frontend::Sink,
        }
    }
}
