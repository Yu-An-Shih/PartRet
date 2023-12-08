#!/usr/bin/env python3

# TODO: license

class Logger():
    """ Logging helper """

    logger_headers = [
        '========================================',
        '  PartRet - partial retention checking  ',
        '========================================',
        ''
    ]

    def __init__(self, log_file):
        """ Set the log file name and print the logger header """

        self._file_name = log_file

        header = '\n'.join(Logger.logger_headers)

        with open(self._file_name, 'w') as fw:
            print(header, file=fw)

        print(header)

    def dump(self, msg):
        """ Print the message to the log file and stdout """

        with open(self._file_name, 'a') as fw:
            print(msg, file=fw)

        print(msg)

    def fence(self):
        """ Print fence seperating logs """

        self.dump('')
        self.dump('==========================================')
        self.dump('')
