#!/usr/bin/env python3

# TODO: license

import json

class Image():
    """ Screenshot image """

    def __init__(self, logger, file_name):
        """ Initialize the image """

        self._logger = logger
        self._file = file_name
        self._image = {}
    
    def take_screenshot(self, ret, nonret, unknown, meta=None):
        """ Record the current progress """

        self._image['retention'] = list(ret)
        self._image['non_retention'] = list(nonret)
        self._image['unknown'] = list(unknown)

        if meta:
            for entry in meta:
                self._image[entry] = list(meta[entry])

        self._dump()

    def _dump(self):
        """ Dump the image to a file """

        self._image['retention'].sort()
        self._image['non_retention'].sort()
        self._image['unknown'].sort()

        with open(self._file, 'w') as fw:
            json.dump(self._image, fw, indent=4)
    